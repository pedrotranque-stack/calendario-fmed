#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
calendario.py - Publica calendarios de Outlook (.ics) como página web, al estilo Outlook

Lee los calendarios publicados de Outlook (enlaces ICS), los junta en una sola página
con vistas Semana, Mes y Agenda, cada calendario con su color y una lista para
activarlos o desactivarlos como en Outlook. Las prácticas y los exámenes se
destacan con borde y etiqueta, y toman el color de su asignatura.

La página se publica en GitHub Pages y se actualiza sola desde GitHub (no hace
falta tener el ordenador encendido). Desde el PC solo se configura.

Uso en el PC:
  python calendario.py --configurar         calendarios, colores, tipos y opciones
  python calendario.py --abrir              generar la página en el PC y abrirla (vista previa)
  python calendario.py --publicar           enviar la configuración a GitHub (la primera vez, la prepara)
  python calendario.py --paleta             ver la paleta de colores con sus códigos
  python calendario.py --abrir-web          abrir la página publicada

Uso en GitHub (lo hace la tarea programada):
  python calendario.py --ci                 lee calendarios.json y el secreto CALENDARIOS_ICS

Requisitos (una sola vez):  pip install requests python-dateutil
Para publicar: Git para Windows (https://git-scm.com/download/win).
"""

import argparse
import hashlib
import io
import json
import math
import os
import re
import secrets as _secrets
import shutil
import subprocess
import sys
import unicodedata
from collections import defaultdict
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta, timezone
from zoneinfo import ZoneInfo

try:
    import requests
    from dateutil import rrule as du_rrule
    from dateutil import tz as du_tz
except ImportError as _e:
    sys.exit(f"Falta la librería '{_e.name}'. Instálalas con:\n"
             f"  pip install requests python-dateutil")

try:
    sys.stdout.reconfigure(errors="replace")
    sys.stderr.reconfigure(errors="replace")
except Exception:
    pass

VERSION = "2.1"
DIR_SCRIPT = os.path.dirname(os.path.abspath(__file__))
CONFIG_DEFECTO = os.path.join(DIR_SCRIPT, "calendarios_config.json")   # local: incluye las direcciones
CONFIG_PUBLICA = os.path.join(DIR_SCRIPT, "calendarios.json")          # en GitHub: sin direcciones
DIR_CACHE = os.path.join(DIR_SCRIPT, "cache_calendarios")
DIR_SALIDA = os.path.join(DIR_SCRIPT, "calendario generado")
DIR_REPO = os.path.join(DIR_SCRIPT, "_repositorio_calendario")
SECRETO = "CALENDARIOS_ICS"
RUTA_WORKFLOW = ".github/workflows/publicar-calendario.yml"
SIN_VENTANA = 0x08000000 if sys.platform.startswith("win") else 0

CONFIG_BASE = {
    "titulo": "Horario",
    "subtitulo": "",
    "zona_horaria": "Europe/Madrid",
    "desde": "auto",          # "auto" = desde el mes anterior al actual; o "AAAA-MM"
    "meses": 6,
    "fin_de_semana": False,   # False = solo de lunes a viernes
    "calendarios": [],
}

TIPOS = {   # clave: (nombre en el menú, encabezado en la página)
    "asignatura": ("asignatura (clases de teoría)", "Asignaturas"),
    "practicas": ("prácticas", "Prácticas"),
    "examenes": ("exámenes", "Exámenes"),
    "otros": ("otros (festivos, eventos...)", "Otros"),
}

# Paleta: nombre, código. Los cinco últimos son los del horario de Psicología.
PALETA = [
    ("azul", "#0078D4"), ("azul cielo", "#4FA3E0"), ("azul marino", "#1B3A6B"),
    ("turquesa", "#038387"), ("cian", "#00B7C3"), ("verde", "#107C10"),
    ("verde lima", "#8CBD18"), ("verde menta", "#00CC6A"), ("amarillo", "#FFC000"),
    ("mostaza", "#986F0B"), ("naranja", "#CA5010"), ("naranja claro", "#FF8C00"),
    ("rojo", "#D13438"), ("granate", "#A4262C"), ("rosa", "#E3008C"),
    ("morado", "#8764B8"), ("lavanda", "#B4A0FF"), ("marrón", "#8E562E"),
    ("gris", "#69797E"), ("gris claro", "#A0A0A0"),
    ("verde pastel", "#B3E5A1"), ("celeste", "#95DCF7"), ("rosa pastel", "#E59EDC"),
    ("melocotón", "#F8C9A0"), ("gris perla", "#D1D1D1"),
]

MESES = ["enero", "febrero", "marzo", "abril", "mayo", "junio", "julio",
         "agosto", "septiembre", "octubre", "noviembre", "diciembre"]

# Nombres de zona horaria de Windows/Outlook -> IANA (los más habituales)
WINDOWS_TZ = {
    "Romance Standard Time": "Europe/Paris",
    "W. Europe Standard Time": "Europe/Berlin",
    "Central Europe Standard Time": "Europe/Budapest",
    "Central European Standard Time": "Europe/Warsaw",
    "GMT Standard Time": "Europe/London",
    "Greenwich Standard Time": "Atlantic/Reykjavik",
    "GTB Standard Time": "Europe/Athens",
    "E. Europe Standard Time": "Europe/Chisinau",
    "FLE Standard Time": "Europe/Helsinki",
    "Russian Standard Time": "Europe/Moscow",
    "Morocco Standard Time": "Africa/Casablanca",
    "Eastern Standard Time": "America/New_York",
    "Central Standard Time": "America/Chicago",
    "Mountain Standard Time": "America/Denver",
    "Pacific Standard Time": "America/Los_Angeles",
    "SA Pacific Standard Time": "America/Bogota",
    "Argentina Standard Time": "America/Buenos_Aires",
    "Central Standard Time (Mexico)": "America/Mexico_City",
    "UTC": "UTC",
    "Coordinated Universal Time": "UTC",
}



# ═════════════════════════════════════════════════════════════════════════════
#  1. LECTURA DE ARCHIVOS .ICS
# ═════════════════════════════════════════════════════════════════════════════

class Componente:
    """Bloque BEGIN:xxx ... END:xxx de un archivo iCalendar."""

    def __init__(self, tipo):
        self.tipo = tipo
        self.props = []      # (NOMBRE, {PARAMS}, valor)
        self.hijos = []
        self.texto = []      # líneas originales (para VTIMEZONE)

    def prop(self, nombre):
        for p in self.props:
            if p[0] == nombre:
                return p
        return None

    def valor(self, nombre, defecto=""):
        p = self.prop(nombre)
        return p[2] if p else defecto

    def todas(self, nombre):
        return [p for p in self.props if p[0] == nombre]

    def buscar(self, tipo):
        for h in self.hijos:
            if h.tipo == tipo:
                yield h
            yield from h.buscar(tipo)


def _dividir_fuera_comillas(texto, sep):
    partes, actual, comillas = [], [], False
    for ch in texto:
        if ch == '"':
            comillas = not comillas
        if ch == sep and not comillas:
            partes.append("".join(actual))
            actual = []
        else:
            actual.append(ch)
    partes.append("".join(actual))
    return partes


def _parsear_linea(linea):
    comillas = False
    for i, ch in enumerate(linea):
        if ch == '"':
            comillas = not comillas
        elif ch == ":" and not comillas:
            cabecera, valor = linea[:i], linea[i + 1:]
            break
    else:
        return None
    partes = _dividir_fuera_comillas(cabecera, ";")
    params = {}
    for p in partes[1:]:
        if "=" in p:
            k, v = p.split("=", 1)
            params[k.strip().upper()] = v.strip().strip('"')
    return partes[0].strip().upper(), params, valor


def parsear_ics(texto):
    """Convierte el texto de un .ics en un árbol de Componentes."""
    texto = texto.lstrip("﻿").replace("\r\n", "\n").replace("\r", "\n")
    lineas = []
    for l in texto.split("\n"):
        if l[:1] in (" ", "\t") and lineas:
            lineas[-1] += l[1:]          # línea plegada (RFC 5545)
        elif l.strip():
            lineas.append(l)
    raiz = Componente("RAIZ")
    pila = [raiz]
    for l in lineas:
        r = _parsear_linea(l)
        if r is None:
            continue
        nombre, params, valor = r
        if nombre == "BEGIN":
            nuevo = Componente(valor.strip().upper())
            pila[-1].hijos.append(nuevo)
            pila.append(nuevo)
        elif nombre == "END":
            if len(pila) > 1:
                pila.pop()
        else:
            pila[-1].props.append((nombre, params, valor))
        for comp in pila[1:]:
            if comp.tipo == "VTIMEZONE":
                comp.texto.append(l)
                break
    return raiz


def _desescapar(t):
    return (t.replace("\\n", " ").replace("\\N", " ").replace("\\,", ",")
             .replace("\\;", ";").replace("\\\\", "\\")).strip()


_PROPS_VTZ = {"TZID", "TZURL", "LAST-MODIFIED", "COMMENT", "TZOFFSETFROM",
              "TZOFFSETTO", "TZNAME", "DTSTART", "RRULE", "RDATE", "BEGIN", "END"}


class ResolutorZonas:
    """Traduce los TZID del calendario a zonas horarias utilizables."""

    def __init__(self, raiz, tz_defecto):
        self.tz_defecto = tz_defecto
        self.cache = {}
        self.vtz = {}
        for comp in raiz.buscar("VTIMEZONE"):
            tzid = comp.valor("TZID").strip().strip('"')
            if tzid:
                self.vtz[tzid] = comp

    def __call__(self, tzid):
        if not tzid:
            return self.tz_defecto
        tzid = tzid.strip().strip('"')
        if tzid not in self.cache:
            self.cache[tzid] = self._resolver(tzid)
        return self.cache[tzid]

    def _resolver(self, tzid):
        candidatos = [tzid]
        m = re.search(r"([A-Za-z]+/[A-Za-z_+\-]+(?:/[A-Za-z_+\-]+)?)$", tzid)
        if m:
            candidatos.append(m.group(1))       # p. ej. /mozilla.org/.../Europe/Madrid
        if tzid in WINDOWS_TZ:
            candidatos.append(WINDOWS_TZ[tzid])
        for c in candidatos:
            try:
                return ZoneInfo(c)
            except Exception:
                pass
        comp = self.vtz.get(tzid)
        if comp is not None:                    # definición propia (Outlook "Customized Time Zone")
            try:
                lineas = [l for l in comp.texto
                          if _parsear_linea(l) and _parsear_linea(l)[0] in _PROPS_VTZ]
                bloque = "BEGIN:VTIMEZONE\n" + "\n".join(lineas) + "\nEND:VTIMEZONE\n"
                z = du_tz.tzical(io.StringIO(bloque)).get()
                if z is not None:
                    return z
            except Exception:
                pass
        return self.tz_defecto


def _parsear_fecha(valor, params, resolutor):
    """Devuelve date (evento de día completo) o datetime con zona horaria."""
    v = valor.strip()
    if params.get("VALUE", "").upper() == "DATE" or re.fullmatch(r"\d{8}", v):
        return date(int(v[:4]), int(v[4:6]), int(v[6:8]))
    m = re.fullmatch(r"(\d{8})T(\d{6})(Z?)", v)
    if not m:
        raise ValueError(f"fecha no reconocida: {v}")
    dt = datetime.strptime(m.group(1) + m.group(2), "%Y%m%d%H%M%S")
    if m.group(3):
        return dt.replace(tzinfo=timezone.utc)
    return dt.replace(tzinfo=resolutor(params.get("TZID")))


def _parsear_lista_fechas(props, resolutor):
    salida = []
    for _, params, valor in props:
        for v in valor.split(","):
            if v.strip():
                try:
                    salida.append(_parsear_fecha(v, params, resolutor))
                except ValueError:
                    pass
    return salida


def _parsear_duracion(v):
    m = re.fullmatch(r"([+-])?P(?:(\d+)W)?(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?",
                     v.strip().upper())
    if not m:
        return timedelta(0)
    sg, w, d, h, mi, s = m.groups()
    td = timedelta(weeks=int(w or 0), days=int(d or 0), hours=int(h or 0),
                   minutes=int(mi or 0), seconds=int(s or 0))
    return -td if sg == "-" else td


def _es_dt(x):
    return isinstance(x, datetime)


def _clave(valor, todo_dia, tz_local):
    """Clave para comparar ocurrencias con EXDATE / RECURRENCE-ID."""
    if todo_dia:
        return valor.astimezone(tz_local).date() if _es_dt(valor) else valor
    if _es_dt(valor):
        return valor.astimezone(timezone.utc).replace(tzinfo=None)
    return datetime.combine(valor, time())


def _normalizar_rrule(txt, tz_evento, todo_dia, tz_local):
    """Ajusta UNTIL para que sea compatible con el DTSTART (sin zona horaria)."""
    txt = txt.strip()
    if txt.upper().startswith("RRULE:"):
        txt = txt[6:]
    partes = []
    for p in txt.split(";"):
        if p.upper().startswith("UNTIL="):
            m = re.fullmatch(r"(\d{8})(?:T(\d{6})(Z)?)?", p[6:].strip())
            if m:
                if m.group(2) is None:
                    u = datetime.strptime(m.group(1), "%Y%m%d") + timedelta(hours=23, minutes=59, seconds=59)
                else:
                    u = datetime.strptime(m.group(1) + m.group(2), "%Y%m%d%H%M%S")
                    if m.group(3):
                        u = u.replace(tzinfo=timezone.utc)
                        destino = tz_local if todo_dia else tz_evento
                        u = u.astimezone(destino).replace(tzinfo=None) if destino else u.replace(tzinfo=None)
                    if todo_dia:
                        u = datetime.combine(u.date(), time(23, 59, 59))
                p = "UNTIL=" + u.strftime("%Y%m%dT%H%M%S")
        partes.append(p)
    return ";".join(partes)


def _expandir(item, w_ini, w_fin, excluidas, tz_local):
    """Fechas de inicio de un evento recurrente dentro de la ventana."""
    ini, todo_dia, dur = item["ini"], item["todo_dia"], item["dur"]
    if todo_dia:
        tz_ev = None
        base = datetime.combine(ini, time())
        wi = datetime.combine(w_ini.date(), time())
        wf = datetime.combine(w_fin.date(), time())
    else:
        tz_ev = ini.tzinfo
        base = ini.replace(tzinfo=None)
        wi = w_ini.astimezone(tz_ev).replace(tzinfo=None)
        wf = w_fin.astimezone(tz_ev).replace(tzinfo=None)
    wi -= dur + timedelta(days=1)
    wf += timedelta(days=1)

    inicios = set()
    for txt in item["rrules"]:
        regla = du_rrule.rrulestr(_normalizar_rrule(txt, tz_ev, todo_dia, tz_local), dtstart=base)
        inicios.update(regla.between(wi, wf, inc=True))
    for rd in item["rdates"]:
        if todo_dia:
            n = datetime.combine(rd.astimezone(tz_local).date() if _es_dt(rd) else rd, time())
        else:
            n = rd.astimezone(tz_ev).replace(tzinfo=None) if _es_dt(rd) else datetime.combine(rd, base.time())
        if wi <= n <= wf:
            inicios.add(n)

    salida = []
    for n in sorted(inicios):
        v = n.date() if todo_dia else n.replace(tzinfo=tz_ev)
        if _clave(v, todo_dia, tz_local) not in excluidas:
            salida.append(v)
    return salida


@dataclass
class Evento:
    titulo: str
    inicio: datetime        # con zona horaria local
    fin: datetime           # exclusivo
    todo_el_dia: bool
    calendario: dict
    ubicacion: str = ""

    @property
    def es_barra(self):
        """Se dibuja como barra: día completo o duración >= 24 h."""
        return self.todo_el_dia or (self.fin - self.inicio) >= timedelta(hours=24)

    @property
    def dia_ini(self):
        return self.inicio.date()

    @property
    def dia_fin(self):
        """Último día que ocupa (inclusive)."""
        if self.fin <= self.inicio:
            return self.inicio.date()
        return (self.fin - timedelta(microseconds=1)).date()


def leer_eventos(texto, cal, w_ini, w_fin, tz_local):
    """Devuelve (eventos, avisos) de un calendario dentro de la ventana [w_ini, w_fin)."""
    avisos = []
    raiz = parsear_ics(texto)
    vcal = next(raiz.buscar("VCALENDAR"), raiz)
    tz_flot = tz_local
    xwr = vcal.valor("X-WR-TIMEZONE").strip()
    if xwr:
        try:
            tz_flot = ZoneInfo(xwr)
        except Exception:
            pass
    resolutor = ResolutorZonas(raiz, tz_flot)

    items = []
    for ev in vcal.buscar("VEVENT"):
        p_ini = ev.prop("DTSTART")
        if not p_ini:
            continue
        try:
            ini = _parsear_fecha(p_ini[2], p_ini[1], resolutor)
            p_fin = ev.prop("DTEND")
            if p_fin:
                fin = _parsear_fecha(p_fin[2], p_fin[1], resolutor)
            elif ev.prop("DURATION"):
                fin = ini + _parsear_duracion(ev.valor("DURATION"))
            else:
                fin = ini if _es_dt(ini) else ini + timedelta(days=1)
            p_rec = ev.prop("RECURRENCE-ID")
            recid = _parsear_fecha(p_rec[2], p_rec[1], resolutor) if p_rec else None
        except Exception as e:
            avisos.append(f"Evento ignorado en '{cal['nombre']}': {e}")
            continue

        todo_dia = (not _es_dt(ini)) or ev.valor("X-MICROSOFT-CDO-ALLDAYEVENT").strip().upper() == "TRUE"
        if todo_dia:
            d_ini = ini.astimezone(tz_local).date() if _es_dt(ini) else ini
            d_fin = fin.astimezone(tz_local).date() if _es_dt(fin) else fin
            if d_fin <= d_ini:
                d_fin = d_ini + timedelta(days=1)
            ini, dur = d_ini, d_fin - d_ini
        else:
            if not _es_dt(fin):
                fin = datetime.combine(fin, time(), ini.tzinfo)
            dur = max(fin - ini, timedelta(0))

        items.append({
            "uid": ev.valor("UID").strip() or f"sin-uid-{len(items)}",
            "titulo": _desescapar(ev.valor("SUMMARY")) or "(sin título)",
            "ubicacion": _desescapar(ev.valor("LOCATION")),
            "cancelado": ev.valor("STATUS").strip().upper() == "CANCELLED",
            "ini": ini, "dur": dur, "todo_dia": todo_dia, "recid": recid,
            "rrules": [p[2] for p in ev.todas("RRULE")],
            "rdates": _parsear_lista_fechas(ev.todas("RDATE"), resolutor),
            "exdates": _parsear_lista_fechas(ev.todas("EXDATE"), resolutor),
        })

    recids_por_uid = defaultdict(list)
    for it in items:
        if it["recid"] is not None:
            recids_por_uid[it["uid"]].append(it["recid"])

    eventos = []
    privado = cal.get("detalle", "completo") == "ocupado"

    def crear(it, inicio):
        if it["todo_dia"]:
            a = datetime.combine(inicio, time(), tz_local)
            b = a + it["dur"]
        else:
            a = inicio.astimezone(tz_local)
            b = (inicio + it["dur"]).astimezone(tz_local)
        if b > w_ini and a < w_fin or (a == b and w_ini <= a < w_fin):
            eventos.append(Evento(
                titulo="Ocupado" if privado else it["titulo"],
                inicio=a, fin=b, todo_el_dia=it["todo_dia"], calendario=cal,
                ubicacion="" if privado else it["ubicacion"]))

    for it in items:
        if it["cancelado"]:
            continue
        if it["rrules"] and it["recid"] is None:
            excl = {_clave(x, it["todo_dia"], tz_local) for x in it["exdates"]}
            excl |= {_clave(x, it["todo_dia"], tz_local) for x in recids_por_uid[it["uid"]]}
            try:
                inicios = _expandir(it, w_ini, w_fin, excl, tz_local)
            except Exception as e:
                avisos.append(f"Repetición no interpretada en '{cal['nombre']}' "
                              f"({it['titulo'][:40]}): {e}")
                inicios = [it["ini"]]
            for s in inicios:
                crear(it, s)
        else:
            crear(it, it["ini"])
    return eventos, avisos


def info_calendario(texto):
    """(nombre interno del calendario, nº de eventos) para mostrar al configurar."""
    raiz = parsear_ics(texto)
    vcal = next(raiz.buscar("VCALENDAR"), raiz)
    return _desescapar(vcal.valor("X-WR-CALNAME")), sum(1 for _ in vcal.buscar("VEVENT"))


# ═════════════════════════════════════════════════════════════════════════════
#  2. DESCARGA (con copia de seguridad local)
# ═════════════════════════════════════════════════════════════════════════════

def _normalizar_origen(origen):
    origen = origen.strip().strip('"').strip("'")
    if origen.lower().startswith("webcal://"):
        origen = "https://" + origen[9:]
    return origen


def descargar_ics(origen):
    origen = _normalizar_origen(origen)
    if re.match(r"https?://", origen, re.I):
        r = requests.get(origen, timeout=40, headers={
            "User-Agent": f"calendario-ics/{VERSION}",
            "Cache-Control": "no-cache", "Pragma": "no-cache"})   # pedir siempre la versión más reciente
        r.raise_for_status()
        texto = r.content.decode("utf-8", errors="replace")
    else:
        ruta = os.path.expanduser(origen)
        if not os.path.isabs(ruta) and not os.path.exists(ruta):
            ruta = os.path.join(DIR_SCRIPT, ruta)     # si no está en la carpeta actual, junto al script
        with open(ruta, "rb") as f:
            texto = f.read().decode("utf-8", errors="replace")
    if "BEGIN:VCALENDAR" not in texto[:5000].upper():
        raise ValueError("no es un calendario .ics (¿has copiado el enlace HTML en lugar del ICS?)")
    return texto


def _ruta_cache(origen):
    h = hashlib.sha1(_normalizar_origen(origen).encode("utf-8")).hexdigest()[:16]
    return os.path.join(DIR_CACHE, f"{h}.ics")


def obtener_ics(cal):
    """Descarga el calendario; si falla, usa la última copia buena. Devuelve (texto, aviso)."""
    try:
        texto = descargar_ics(cal["origen"])
        try:
            os.makedirs(DIR_CACHE, exist_ok=True)
            with open(_ruta_cache(cal["origen"]), "w", encoding="utf-8") as f:
                f.write(texto)
        except OSError:
            pass
        return texto, None
    except Exception as e:
        ruta = _ruta_cache(cal["origen"])
        if os.path.exists(ruta):
            cuando = datetime.fromtimestamp(os.path.getmtime(ruta)).strftime("%d/%m/%Y %H:%M")
            with open(ruta, encoding="utf-8") as f:
                return f.read(), (f"'{cal['nombre']}' no se pudo actualizar; "
                                  f"se usa la copia del {cuando}")
        return None, f"'{cal['nombre']}' no se pudo leer ({_resumir_error(e)})"


def _resumir_error(e):
    t = str(e)
    return (t[:120] + "...") if len(t) > 120 else t



# ═════════════════════════════════════════════════════════════════════════════
#  3. DATOS PARA LA PÁGINA
# ═════════════════════════════════════════════════════════════════════════════

def _sin_acentos(t):
    return unicodedata.normalize("NFKD", t).encode("ascii", "ignore").decode().lower()


def _hex_valido(h):
    return h.upper() if re.fullmatch(r"#[0-9A-Fa-f]{6}", str(h or "")) else "#69797E"


def _palabras(cal):
    """Palabras con las que se reconoce una asignatura en los títulos de prácticas y exámenes."""
    txt = cal.get("palabras") or cal["nombre"]
    return [p for p in (_sin_acentos(x).strip() for x in txt.split(",")) if len(p) >= 2]


_RE_GRUPO = re.compile(r"\bG\s?(\d{1,2})(?:\s*(?:y|e|,|/|-)\s*G?\s?(\d{1,2}))?\b", re.I)


def clasificar(ev, cal, asignaturas):
    """Devuelve (tipo, clave de la asignatura para el color, grupos)."""
    tipo_cal = cal.get("tipo", "asignatura")
    t = _sin_acentos(ev.titulo)
    if tipo_cal == "examenes" or re.search(r"\bexamen", t):
        tipo = "examen"
    elif tipo_cal == "practicas" or re.search(r"\bpractica", t):
        tipo = "practica"
    elif tipo_cal == "otros":
        tipo = "otro"
    else:
        tipo = "teoria"
    asig = cal["clave"] if tipo_cal == "asignatura" else None
    if asig is None and tipo != "otro":
        mejor = 0
        for a in asignaturas:                      # la coincidencia más larga gana
            for p in _palabras(a):
                if len(p) > mejor and re.search(r"(?<![a-z0-9])" + re.escape(p) + r"(?![a-z0-9])", t):
                    asig, mejor = a["clave"], len(p)
    grupos = []
    m = _RE_GRUPO.search(ev.titulo)
    if m:
        grupos = ["G" + str(int(m.group(1)))] + (["G" + str(int(m.group(2)))] if m.group(2) else [])
    return tipo, asig, grupos


def ventana(cfg, ahora):
    """Primer día incluido y día siguiente al último."""
    desde = str(cfg.get("desde") or "auto").strip()
    m = re.fullmatch(r"(\d{4})-(\d{1,2})", desde)
    if m:
        y, mes = int(m.group(1)), int(m.group(2))
    else:
        y, mes = (ahora.year, ahora.month - 1) if ahora.month > 1 else (ahora.year - 1, 12)
    n = max(1, int(cfg.get("meses") or 6))
    a, b = divmod(mes - 1 + n, 12)
    return date(y, mes, 1), date(y + a, b + 1, 1)


def recoger(cfg, direcciones=None):
    """Lee los calendarios activos. direcciones: {clave: url} (en GitHub, del secreto)."""
    tz = ZoneInfo(cfg.get("zona_horaria") or "Europe/Madrid")
    ahora = datetime.now(tz)
    d_ini, d_fin = ventana(cfg, ahora)
    w_ini = datetime.combine(d_ini, time(), tz)
    w_fin = datetime.combine(d_fin, time(), tz)
    activos = [c for c in cfg["calendarios"] if c.get("activo", True)]
    asignaturas = [c for c in activos if c.get("tipo", "asignatura") == "asignatura"]
    eventos, avisos, leidos = [], [], 0
    for cal in activos:
        cal = dict(cal)
        if direcciones is not None:
            cal["origen"] = direcciones.get(cal["clave"], "")
            if not cal["origen"]:
                avisos.append(f"Falta la dirección de «{cal['nombre']}» en el secreto {SECRETO}")
                print("  AVISO:", avisos[-1])
                continue
        texto, aviso = obtener_ics(cal)
        if aviso:
            avisos.append(aviso)
            print("  AVISO:", aviso)
        if texto is None:
            continue
        leidos += 1
        evs, avs = leer_eventos(texto, cal, w_ini, w_fin, tz)
        for a in avs[:5]:
            print("  AVISO:", a)
        print(f"  {cal['nombre']}: {len(evs)} eventos")
        for ev in evs:
            tipo, asig, grupos = clasificar(ev, cal, asignaturas)
            if ev.todo_el_dia:
                i, f = ev.inicio.date().isoformat(), ev.fin.date().isoformat()
            else:
                i, f = ev.inicio.strftime("%Y-%m-%dT%H:%M"), ev.fin.strftime("%Y-%m-%dT%H:%M")
            eventos.append({"c": cal["clave"], "a": asig, "tipo": tipo, "t": ev.titulo, "u": ev.ubicacion,
                            "g": grupos, "i": i, "f": f, "td": ev.todo_el_dia})
    eventos.sort(key=lambda e: (e["i"], e["t"]))
    datos = {
        "titulo": cfg.get("titulo") or "Horario",
        "subtitulo": cfg.get("subtitulo") or "",
        "zona": cfg.get("zona_horaria"),
        "dias": 7 if cfg.get("fin_de_semana") else 5,
        "rango": [d_ini.isoformat(), (d_fin - timedelta(days=1)).isoformat()],
        "calendarios": [{"clave": c["clave"], "nombre": c["nombre"], "color": _hex_valido(c.get("color")),
                         "tipo": c.get("tipo", "asignatura")} for c in activos],
        "eventos": eventos,
        "avisos": avisos[:4],
    }
    return datos, leidos, ahora


def pagina_html(datos, ahora):
    datos = dict(datos, actualizado=ahora.strftime("%d/%m/%Y %H:%M"))
    js = json.dumps(datos, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    import html as _html
    return (PLANTILLA.replace("__DATOS__", js)
            .replace("__TITULO__", _html.escape(datos["titulo"]))
            .replace("__VERSION__", VERSION))


def _huella(datos):
    return hashlib.sha256(json.dumps(datos, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def _escribir(ruta, texto):
    os.makedirs(os.path.dirname(ruta) or ".", exist_ok=True)
    tmp = ruta + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(texto)
    os.replace(tmp, ruta)


# ═════════════════════════════════════════════════════════════════════════════
#  4. GENERACIÓN (en el PC y en GitHub)
# ═════════════════════════════════════════════════════════════════════════════

def generar_local(cfg):
    print("Leyendo calendarios...")
    datos, leidos, ahora = recoger(cfg)
    if not leidos:
        sys.exit("ERROR: no se pudo leer ningún calendario.")
    ruta = os.path.join(DIR_SALIDA, "index.html")
    _escribir(ruta, pagina_html(datos, ahora))
    print(f"\nVista previa: {ruta}  ({len(datos['eventos'])} eventos)")
    return ruta


def leer_secreto(crudo):
    """Admite el formato JSON del menú aunque lleve caracteres invisibles o texto alrededor."""
    limpio = crudo.replace("\ufeff", "").replace("\u200b", "").strip()
    i, j = limpio.find("{"), limpio.rfind("}")
    if i >= 0 and j > i:
        try:
            datos = json.loads(limpio[i:j + 1])
            if isinstance(datos, dict):
                return {str(k): str(v).strip() for k, v in datos.items() if str(v).strip()}
        except json.JSONDecodeError:
            pass
    datos = {}                                   # alternativa: una línea "clave: url" por calendario
    for m in re.finditer(r'"?([A-Za-z0-9_-]+)"?\s*[:=]\s*"?((?:https?|webcal)://[^"\s,]+)', limpio):
        datos[m.group(1)] = m.group(2)
    return datos


def modo_ci():
    """Lo ejecuta la tarea programada de GitHub."""
    if not os.path.exists(CONFIG_PUBLICA):
        sys.exit(f"No se encuentra {os.path.basename(CONFIG_PUBLICA)} en el repositorio.")
    cfg = cargar_config(CONFIG_PUBLICA)
    crudo = os.environ.get(SECRETO, "")
    if not crudo.strip():
        sys.exit(f"Falta el secreto {SECRETO} (Settings > Secrets and variables > Actions).")
    direcciones = leer_secreto(crudo)
    if not direcciones:
        limpio = crudo.replace("\ufeff", "").strip()
        sys.exit(f"El secreto {SECRETO} no tiene el formato correcto ({len(limpio)} caracteres; "
                 f"{'empieza' if limpio.startswith('{') else 'no empieza'} por '{{'). "
                 "Vuelve a copiarlo con la opción 'Volver a pegar el secreto' del menú del PC.")
    datos, leidos, ahora = recoger(cfg, direcciones)
    if not leidos:
        sys.exit("ERROR: no se pudo leer ningún calendario; no se publica nada.")
    huella = _huella(datos)
    ruta_h = os.path.join(DIR_CACHE, "ultima_publicacion.txt")
    anterior = open(ruta_h).read().strip() if os.path.exists(ruta_h) else ""
    forzado = os.environ.get("GITHUB_EVENT_NAME") in ("push", "workflow_dispatch")
    cambiado = forzado or huella != anterior
    if cambiado:
        _escribir(os.path.join(DIR_SCRIPT, "_site", "index.html"), pagina_html(datos, ahora))
        os.makedirs(DIR_CACHE, exist_ok=True)
        with open(ruta_h, "w") as f:
            f.write(huella)
    print(f"{len(datos['eventos'])} eventos · " + ("hay cambios: se publica" if cambiado else "sin cambios"))
    salida = os.environ.get("GITHUB_OUTPUT")
    if salida:
        with open(salida, "a") as f:
            f.write(f"cambiado={'true' if cambiado else 'false'}\n")


# ═════════════════════════════════════════════════════════════════════════════
#  5. CONFIGURACIÓN INTERACTIVA
# ═════════════════════════════════════════════════════════════════════════════

def cargar_config(ruta):
    if not os.path.exists(ruta):
        return None
    with open(ruta, encoding="utf-8") as f:
        cfg = json.load(f)
    for k in ("solo_laborables", "formato", "salida", "agenda"):    # opciones de versiones anteriores
        cfg.pop(k, None)
    for k, v in CONFIG_BASE.items():
        cfg.setdefault(k, v if not isinstance(v, list) else [])
    for c in cfg["calendarios"]:
        c.setdefault("clave", "c" + _secrets.token_hex(3))
        c.setdefault("tipo", "asignatura")
        c.setdefault("activo", True)
    return cfg


def guardar_config(cfg, ruta):
    tmp = ruta + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    os.replace(tmp, ruta)


class Salir(Exception):
    pass


def _preguntar(texto, defecto=None):
    sufijo = f" [{defecto}]" if defecto not in (None, "") else ""
    try:
        r = input(f"{texto}{sufijo}: ").strip()
    except EOFError:
        raise Salir()
    return r if r else (defecto if defecto is not None else "")


def _si(texto, defecto="s"):
    return _preguntar(texto + " (s/n)", defecto).lower().startswith("s")


def _ocultar(origen, n=22):
    o = (origen or "").strip()
    return o if len(o) <= n else o[:n - 9] + "..." + o[-6:]


def _color_consola():
    if not sys.stdout.isatty():
        return False
    if sys.platform.startswith("win"):
        os.system("")              # activa los colores en la consola de Windows
    return True


def _muestra(hexstr):
    if not _COLOR:
        return ""
    h = _hex_valido(hexstr)
    r, g, b = (int(h[i:i + 2], 16) for i in (1, 3, 5))
    return f"\033[38;2;{r};{g};{b}m██\033[0m "


def _nombre_color(hexstr):
    for n, h in PALETA:
        if h.lower() == str(hexstr).lower():
            return n
    return str(hexstr)


def mostrar_paleta():
    print("\nPALETA DE COLORES (número, nombre y código)\n")
    filas = math.ceil(len(PALETA) / 3)
    for f in range(filas):
        linea = ""
        for col in range(3):
            i = f + col * filas
            if i < len(PALETA):
                n, h = PALETA[i]
                linea += f"  {_muestra(h)}{i + 1:>2}) {n:<14}{h}   "
        print(linea)
    print("\n  Se puede usar cualquier otro color escribiendo su código, p. ej. #FF8800.")


def _elegir_color(defecto):
    mostrar_paleta()
    while True:
        r = _preguntar("  Color (número, nombre o código)", _nombre_color(defecto)).strip()
        if re.fullmatch(r"#?[0-9A-Fa-f]{6}", r):
            return ("#" + r.lstrip("#")).upper()
        if r.isdigit() and 1 <= int(r) <= len(PALETA):
            return PALETA[int(r) - 1][1]
        for n, h in PALETA:
            if _sin_acentos(r) == _sin_acentos(n):
                return h
        print("  Color no reconocido.")


def _elegir_tipo(defecto="asignatura"):
    claves = list(TIPOS)
    for i, k in enumerate(claves, 1):
        print(f"   {i}) {TIPOS[k][0]}")
    while True:
        r = _preguntar("  Tipo de calendario", str(claves.index(defecto) + 1))
        if r.isdigit() and 1 <= int(r) <= len(claves):
            return claves[int(r) - 1]
        print("  Escribe un número de la lista.")


def _elegir_indice(cfg, texto):
    if not cfg["calendarios"]:
        print("  No hay calendarios todavía.")
        return None
    r = _preguntar(texto)
    if r.isdigit() and 1 <= int(r) <= len(cfg["calendarios"]):
        return int(r) - 1
    print("  Número no válido.")
    return None


def _mostrar(cfg):
    print("\n" + "=" * 80)
    print(" CALENDARIOS")
    print("=" * 80)
    if not cfg["calendarios"]:
        print("  (ninguno todavía: usa la opción 'a' para añadir el primero)")
    for i, c in enumerate(cfg["calendarios"], 1):
        marca = "[x]" if c.get("activo", True) else "[ ]"
        det = " (solo 'Ocupado')" if c.get("detalle") == "ocupado" else ""
        print(f"  {i:>2} {marca} {_muestra(c.get('color'))}{c['nombre'][:24]:<24} "
              f"{TIPOS[c.get('tipo', 'asignatura')][1]:<12} {_nombre_color(c.get('color')):<13}"
              f"{_ocultar(c.get('origen'))}{det}")
    print("-" * 80)
    print(f"  Título: {cfg['titulo']}  |  Desde: {cfg['desde']}  |  Meses: {cfg['meses']}  |  "
          f"Días: {'semana completa' if cfg.get('fin_de_semana') else 'lunes a viernes'}")
    print("-" * 80)
    print("  a) Añadir calendario            s) Elegir qué calendarios se publican ([x])")
    print("  c) Cambiar color                t) Cambiar tipo (asignatura/prácticas/exámenes/otros)")
    print("  r) Renombrar                    d) Detalle: títulos / solo 'Ocupado'")
    print("  e) Eliminar calendario          o) Opciones (título, meses, fin de semana...)")
    print("  p) Probar: ver próximos eventos y cómo se clasifican      l) Ver la paleta de colores")
    print("  g) Guardar y salir              q) Salir sin guardar")


def _anadir(cfg):
    print("\nPega la dirección ICS del calendario publicado en Outlook (o la ruta a un archivo .ics)")
    origen = _preguntar("Dirección").strip().strip('"').strip("'")
    if not origen:
        return
    if "github.com" in origen.lower() or "github.io" in origen.lower():
        print("  Esa es una dirección de GitHub. Aquí va el vínculo ICS del calendario de Outlook:\n"
              "  Outlook > Configuración > Calendario > Calendarios compartidos > Publicar un calendario >\n"
              "  'Puede ver todos los detalles' > Publicar > copiar el vínculo ICS.\n"
              "  La dirección de GitHub se pide en la opción 3 del menú (Publicar en GitHub).")
        return
    if re.match(r"^[\w.-]+\.[a-z]{2,}/", origen, re.I) and not os.path.exists(origen):
        origen = "https://" + origen            # pegada sin https://
    print("  Comprobando...")
    nombre_ics = ""
    try:
        nombre_ics, n = info_calendario(descargar_ics(origen))
        print(f"  OK: calendario leído" + (f" «{nombre_ics}»" if nombre_ics else "") + f", {n} eventos.")
    except Exception as e:
        print(f"  No se pudo leer: {_resumir_error(e)}")
        if not _si("  ¿Añadirlo igualmente?", "n"):
            return
    nombre = _preguntar("Nombre que verá la gente en la página",
                        nombre_ics or f"Calendario {len(cfg['calendarios']) + 1}")
    tipo = _elegir_tipo()
    cal = {"clave": "c" + _secrets.token_hex(3), "nombre": nombre, "origen": _normalizar_origen(origen),
           "tipo": tipo, "detalle": "completo", "activo": True}
    if tipo == "asignatura":
        cal["palabras"] = _preguntar("  Palabras para reconocer esta asignatura en los títulos de prácticas "
                                     "y exámenes (separadas por comas)", nombre)
    usados = {c.get("color", "").lower() for c in cfg["calendarios"]}
    libre = "#D13438" if tipo == "examenes" else next((h for _, h in PALETA if h.lower() not in usados), PALETA[0][1])
    cal["color"] = _elegir_color(libre)
    if _si("¿Mostrar solo 'Ocupado' en lugar de los títulos?", "n"):
        cal["detalle"] = "ocupado"
    cfg["calendarios"].append(cal)
    print(f"  Añadido «{nombre}».")


def _seleccionar(cfg):
    if not cfg["calendarios"]:
        print("  No hay calendarios todavía.")
        return
    for i, c in enumerate(cfg["calendarios"], 1):
        print(f"   {i}) {c['nombre']}")
    actuales = ",".join(str(i) for i, c in enumerate(cfg["calendarios"], 1) if c.get("activo", True))
    r = _preguntar("Números de los calendarios que se publican, separados por comas (o 'todos')",
                   actuales or "todos")
    elegidos = (set(range(1, len(cfg["calendarios"]) + 1)) if r.lower() == "todos"
                else {int(x) for x in re.findall(r"\d+", r) if 1 <= int(x) <= len(cfg["calendarios"])})
    if not elegidos:
        print("  Debes elegir al menos uno. No se ha cambiado nada.")
        return
    for i, c in enumerate(cfg["calendarios"], 1):
        c["activo"] = i in elegidos


def _opciones(cfg):
    cfg["titulo"] = _preguntar("Título de la página", cfg["titulo"])
    cfg["subtitulo"] = _preguntar("Subtítulo (p. ej. 'Primer semestre · curso 2026/27'; '-' para ninguno)",
                                  cfg.get("subtitulo") or "-")
    if cfg["subtitulo"] == "-":
        cfg["subtitulo"] = ""
    while True:
        d = _preguntar("Primer mes que se muestra: 'auto' (el mes anterior al actual) o AAAA-MM", cfg["desde"])
        if d == "auto" or re.fullmatch(r"\d{4}-\d{1,2}", d):
            cfg["desde"] = d
            break
    while True:
        m = _preguntar("Número de meses que se muestran", str(cfg["meses"]))
        if m.isdigit() and 1 <= int(m) <= 24:
            cfg["meses"] = int(m)
            break
    cfg["fin_de_semana"] = _si("¿Mostrar también sábados y domingos?", "s" if cfg.get("fin_de_semana") else "n")
    while True:
        z = _preguntar("Zona horaria", cfg["zona_horaria"])
        try:
            ZoneInfo(z)
            cfg["zona_horaria"] = z
            break
        except Exception:
            print("  Zona no válida (ejemplo: Europe/Madrid).")


def _probar(cfg):
    tz = ZoneInfo(cfg["zona_horaria"])
    ahora = datetime.now(tz)
    activos = [c for c in cfg["calendarios"] if c.get("activo", True)]
    asignaturas = [c for c in activos if c.get("tipo", "asignatura") == "asignatura"]
    nombres = {c["clave"]: c["nombre"] for c in activos}
    for cal in activos:
        print(f"\n  {cal['nombre']} ({TIPOS[cal.get('tipo', 'asignatura')][1]}):")
        texto, aviso = obtener_ics(cal)
        if aviso:
            print("   ", aviso)
        if texto is None:
            continue
        evs, avs = leer_eventos(texto, cal, ahora - timedelta(days=1), ahora + timedelta(days=60), tz)
        print(f"    {len(evs)} eventos en los próximos 60 días.")
        for ev in sorted(evs, key=lambda e: e.inicio)[:5]:
            tipo, asig, grupos = clasificar(ev, cal, asignaturas)
            cuando = f"{ev.inicio:%d/%m}" + ("" if ev.todo_el_dia else f" {ev.inicio:%H:%M}")
            extra = [tipo] + ([f"color de {nombres.get(asig)}"] if asig and asig != cal["clave"] else []) + grupos
            print(f"     - {cuando:<12} {ev.titulo[:42]:<42} [{', '.join(extra)}]")
        for a in avs[:3]:
            print("    AVISO:", a)


def configurar(ruta_cfg):
    """Asistente interactivo. Devuelve True si se quiere ver la vista previa a continuación."""
    cfg = cargar_config(ruta_cfg) or json.loads(json.dumps(CONFIG_BASE))
    print(f"\nConfiguración: {ruta_cfg}")
    try:
        while True:
            _mostrar(cfg)
            op = _preguntar("\nOpción").lower()[:1]
            if op == "a":
                _anadir(cfg)
            elif op == "s":
                _seleccionar(cfg)
            elif op == "c":
                i = _elegir_indice(cfg, "Número del calendario")
                if i is not None:
                    cfg["calendarios"][i]["color"] = _elegir_color(cfg["calendarios"][i].get("color"))
            elif op == "t":
                i = _elegir_indice(cfg, "Número del calendario")
                if i is not None:
                    c = cfg["calendarios"][i]
                    c["tipo"] = _elegir_tipo(c.get("tipo", "asignatura"))
                    if c["tipo"] == "asignatura":
                        c["palabras"] = _preguntar("  Palabras para reconocerla en títulos de prácticas y "
                                                   "exámenes (separadas por comas)", c.get("palabras") or c["nombre"])
            elif op == "d":
                i = _elegir_indice(cfg, "Número del calendario")
                if i is not None:
                    c = cfg["calendarios"][i]
                    c["detalle"] = "completo" if c.get("detalle") == "ocupado" else "ocupado"
                    print(f"  «{c['nombre']}» mostrará: "
                          + ("solo 'Ocupado'" if c["detalle"] == "ocupado" else "los títulos"))
            elif op == "r":
                i = _elegir_indice(cfg, "Número del calendario")
                if i is not None:
                    cfg["calendarios"][i]["nombre"] = _preguntar("Nuevo nombre", cfg["calendarios"][i]["nombre"])
            elif op == "e":
                i = _elegir_indice(cfg, "Número del calendario a eliminar")
                if i is not None and _si(f"  ¿Eliminar «{cfg['calendarios'][i]['nombre']}»?", "n"):
                    cfg["calendarios"].pop(i)
            elif op == "o":
                _opciones(cfg)
            elif op == "p":
                _probar(cfg)
            elif op == "l":
                mostrar_paleta()
            elif op == "g":
                guardar_config(cfg, ruta_cfg)
                print(f"Configuración guardada en {ruta_cfg}")
                print("Recuerda: para que los cambios lleguen a la web, usa 'Publicar en GitHub'.")
                if not any(c.get("activo", True) for c in cfg["calendarios"]):
                    return False
                return _si("¿Ver ahora la vista previa en tu navegador?", "s")
            elif op == "q":
                if _si("¿Salir sin guardar los cambios?", "n"):
                    return False
            else:
                print("  Opción no reconocida.")
    except (Salir, KeyboardInterrupt):
        print("\nSalida sin guardar.")
        return False


# ═════════════════════════════════════════════════════════════════════════════
#  6. PUBLICACIÓN EN GITHUB
# ═════════════════════════════════════════════════════════════════════════════

WORKFLOW = """\
# Generado por calendario.py: descarga los calendarios de Outlook y publica la página.
name: Publicar calendario
on:
  push:
    branches: [main]
  schedule:
    - cron: "7,27,47 * * * *"     # cada 20 minutos
  workflow_dispatch:
permissions:
  contents: write
  pages: write
  id-token: write
concurrency:
  group: publicar-calendario
  cancel-in-progress: false
jobs:
  generar:
    runs-on: ubuntu-latest
    outputs:
      cambiado: ${{ steps.generar.outputs.cambiado }}
    steps:
      - uses: actions/checkout@v6
      - uses: actions/setup-python@v6
        with:
          python-version: "3.12"
      - run: pip install requests python-dateutil
      - name: Recuperar la última copia de los calendarios
        uses: actions/cache/restore@v5
        with:
          path: cache_calendarios
          key: calendarios-${{ github.run_id }}
          restore-keys: calendarios-
      - name: Generar la página
        id: generar
        env:
          CALENDARIOS_ICS: ${{ secrets.CALENDARIOS_ICS }}
        run: python calendario.py --ci
      - name: Guardar la copia de los calendarios
        if: steps.generar.outputs.cambiado == 'true'
        uses: actions/cache/save@v5
        with:
          path: cache_calendarios
          key: calendarios-${{ github.run_id }}
      - name: Preparar la web
        if: steps.generar.outputs.cambiado == 'true'
        uses: actions/upload-pages-artifact@v5
        with:
          path: _site
      - name: Mantener activa la tarea programada
        if: github.event_name == 'schedule'
        run: |
          ultimo=$(git log -1 --format=%ct)
          if [ $(( $(date +%s) - ultimo )) -gt 3888000 ]; then
            git config user.name "github-actions[bot]"
            git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
            date -u > .mantener_activo
            git add .mantener_activo
            git commit -m "Mantener activa la tarea programada"
            git push
          fi
  publicar:
    needs: generar
    if: needs.generar.outputs.cambiado == 'true'
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.despliegue.outputs.page_url }}
    steps:
      - id: despliegue
        uses: actions/deploy-pages@v5
"""

GITIGNORE = "cache_calendarios/\n_site/\n__pycache__/\ncalendarios_config.json\n"


def _git(*args, cwd=DIR_REPO, capturar=True, timeout=300):
    try:
        return subprocess.run(["git", *args], cwd=cwd, timeout=timeout, capture_output=capturar,
                              text=True, encoding="utf-8", errors="replace", creationflags=SIN_VENTANA)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(args, 1, "", "tiempo de espera agotado")
    except FileNotFoundError:
        return subprocess.CompletedProcess(args, 127, "", "git no está instalado")


def _salida(r):
    return ((r.stderr or "") + (r.stdout or "")).strip()


def _partes_repo(url):
    m = re.match(r"(?:https?://|git@)github\.com[/:]([^/]+)/([^/]+?)(?:\.git)?/?$", url.strip())
    return (m.group(1), m.group(2)) if m else (None, None)


def _web_de(url):
    u, r = _partes_repo(url)
    if not u:
        return ""
    return f"https://{u.lower()}.github.io/" if r.lower() == f"{u.lower()}.github.io" else f"https://{u.lower()}.github.io/{r}/"


def _copiar_portapapeles(texto):
    try:
        if sys.platform.startswith("win"):
            subprocess.run(["clip"], input=texto.encode("ascii", "ignore"), check=True, creationflags=SIN_VENTANA)
            return True
        for cmd in (["pbcopy"], ["xclip", "-selection", "clipboard"]):
            if shutil.which(cmd[0]):
                subprocess.run(cmd, input=texto.encode(), check=True)
                return True
    except Exception:
        pass
    return False


def _abrir_web(url):
    try:
        import webbrowser
        webbrowser.open(url)
    except Exception:
        pass


def _config_publica(cfg):
    pub = {k: v for k, v in cfg.items() if k in CONFIG_BASE and k != "calendarios"}
    pub["calendarios"] = [{k: v for k, v in c.items() if k != "origen"} for c in cfg["calendarios"]]
    return pub


def _secreto(cfg):
    return json.dumps({c["clave"]: c["origen"] for c in cfg["calendarios"]
                       if c.get("activo", True) and c.get("origen")}, ensure_ascii=True)


def _esperar(texto="Pulsa Intro cuando lo hayas hecho"):
    try:
        input(f"\n  >> {texto}... ")
    except EOFError:
        pass


def volver_a_pegar_secreto(ruta_cfg):
    cfg = cargar_config(ruta_cfg)
    gh = (cfg or {}).get("github") or {}
    if not gh.get("repositorio"):
        print("La publicación en GitHub no está preparada todavía: usa primero 'Publicar en GitHub'.")
        return False
    usuario, repo = _partes_repo(gh["repositorio"])
    secreto = _secreto(cfg)
    if _copiar_portapapeles(secreto):
        print("Las direcciones de los calendarios están copiadas en el portapapeles.")
    else:
        print("No se pudo usar el portapapeles: copia este texto (es privado):\n\n" + secreto + "\n")
    print(f"En la página que se abre: Value = borrar todo, pegar (Ctrl+V) y pulsar 'Update secret'.")
    print(f"(Si dice que no existe: Settings > Secrets and variables > Actions > New repository secret,\n"
          f" Name = {SECRETO}, Secret = pegar, Add secret.)")
    _abrir_web(f"https://github.com/{usuario}/{repo}/settings/secrets/actions/{SECRETO}")
    _esperar("Pulsa Intro cuando lo hayas guardado")
    gh["secreto"] = hashlib.sha256(secreto.encode()).hexdigest()[:16]
    guardar_config(cfg, ruta_cfg)
    print(f"\nAhora, en GitHub: Actions > la ejecución fallida > 'Re-run jobs' (o espera a la próxima comprobación).")
    print(f"  https://github.com/{usuario}/{repo}/actions")
    return True


def publicar(ruta_cfg, rehacer=False):
    cfg = cargar_config(ruta_cfg)
    if not cfg or not any(c.get("activo", True) for c in cfg["calendarios"]):
        print("Primero configura al menos un calendario (opción 'Configurar calendarios').")
        return False
    if not shutil.which("git"):
        print("No se encuentra Git. Instálalo desde https://git-scm.com/download/win (opciones por defecto),\n"
              "cierra esta ventana y vuelve a abrir el menú.")
        return False
    gh = cfg.setdefault("github", {})

    # 1) Repositorio
    if rehacer or not gh.get("repositorio"):
        print("\n" + "=" * 80 + "\n PREPARAR LA PUBLICACIÓN EN GITHUB (una sola vez)\n" + "=" * 80)
        print("1. En github.com crea un repositorio nuevo: botón + > New repository")
        print("   Nombre: p. ej. calendario-fmed · Public · marca 'Add a README file' · Create repository")
        print("2. Copia la dirección del navegador, p. ej. https://github.com/tu-usuario/calendario-fmed")
        try:
            url = _preguntar("\nDirección del repositorio", gh.get("repositorio")).strip().rstrip("/")
        except Salir:
            return False
        if not _partes_repo(url)[0]:
            print("No parece una dirección de GitHub (https://github.com/usuario/repositorio).")
            return False
        if not url.endswith(".git"):
            url += ".git"
        print("Comprobando el acceso...")
        r = _git("ls-remote", "--symref", url, "HEAD", cwd=DIR_SCRIPT, timeout=120)
        if r.returncode != 0:
            print("No se puede acceder:", _salida(r))
            return False
        m = re.search(r"ref: refs/heads/(\S+)\s+HEAD", r.stdout)
        gh.update(repositorio=url, rama=m.group(1) if m else "main", web=_web_de(url))
        gh.pop("secreto", None)
        gh.pop("pages", None)
        guardar_config(cfg, ruta_cfg)
    usuario, repo = _partes_repo(gh["repositorio"])
    base = f"https://github.com/{usuario}/{repo}"

    # 2) Secreto con las direcciones (solo si han cambiado)
    secreto = _secreto(cfg)
    huella = hashlib.sha256(secreto.encode()).hexdigest()[:16]
    if gh.get("secreto") != huella:
        nuevo = not gh.get("secreto")
        print("\n" + "-" * 80)
        print(f" {'GUARDAR' if nuevo else 'ACTUALIZAR'} LAS DIRECCIONES DE LOS CALENDARIOS (secreto cifrado de GitHub)")
        print("-" * 80)
        copiado = _copiar_portapapeles(secreto)
        print("  Las direcciones están copiadas en el portapapeles." if copiado else
              "  No se pudo usar el portapapeles: copia el texto que aparece a continuación (es privado).")
        if not copiado:
            print("\n" + secreto + "\n")
        if nuevo:
            print(f"  En la página que se abre: Name = {SECRETO} · Secret = pegar (Ctrl+V) · Add secret")
            _abrir_web(f"{base}/settings/secrets/actions/new")
        else:
            print(f"  En la página que se abre: Value = borrar todo y pegar (Ctrl+V) · Update secret")
            _abrir_web(f"{base}/settings/secrets/actions/{SECRETO}")
        print(f"  (Si no se abre: {base} > Settings > Secrets and variables > Actions)")
        _esperar("Pulsa Intro cuando lo hayas guardado")
        gh["secreto"] = huella
        guardar_config(cfg, ruta_cfg)

    # 3) GitHub Pages (una vez)
    if not gh.get("pages"):
        print("\n" + "-" * 80 + "\n ACTIVAR LA WEB (GitHub Pages)\n" + "-" * 80)
        print("  En la página que se abre: Build and deployment > Source: 'GitHub Actions'.")
        print("  (No hace falta pulsar nada más: se guarda solo.)")
        _abrir_web(f"{base}/settings/pages")
        _esperar()
        gh["pages"] = True
        guardar_config(cfg, ruta_cfg)

    # 4) Subir script, tarea programada y configuración pública
    if not _preparar_repo(gh):
        return False
    archivos = {
        "calendario.py": open(os.path.abspath(__file__), encoding="utf-8").read(),
        RUTA_WORKFLOW: WORKFLOW,
        "calendarios.json": json.dumps(_config_publica(cfg), ensure_ascii=False, indent=2) + "\n",
        ".gitignore": GITIGNORE,
    }
    for ruta, contenido in archivos.items():
        _escribir(os.path.join(DIR_REPO, ruta), contenido)
    if not os.path.exists(os.path.join(DIR_REPO, "README.md")) or rehacer:
        _escribir(os.path.join(DIR_REPO, "README.md"),
                  f"# {cfg['titulo']}\n\nCalendario publicado automáticamente con `calendario.py` a partir de "
                  f"calendarios de Outlook.\n\nWeb: {gh.get('web')}\n\nNo editar a mano: la configuración se "
                  "envía desde el menú del PC.\n")
    _git("add", "-A")
    if _git("diff", "--cached", "--quiet").returncode == 0:
        print("\nGitHub ya tiene esta configuración: no hay nada que subir.")
    else:
        _git("commit", "-m", f"Configuración {datetime.now():%d/%m/%Y %H:%M}")
        print("\nSubiendo a GitHub (la primera vez se abrirá una ventana para iniciar sesión)...")
        r = _git("push", "-u", "origin", f"HEAD:{gh.get('rama', 'main')}", capturar=False)
        if r.returncode != 0:
            print("ERROR al subir a GitHub.", _salida(r))
            return False
    print("\nListo. GitHub está generando la página (1-3 minutos).")
    print(f"  Progreso: {base}/actions")
    print(f"  Web:      {gh.get('web')}")
    print("  Después se actualiza sola cada 20 minutos con los cambios de Outlook.")
    return True


def _preparar_repo(gh):
    url, rama = gh["repositorio"], gh.get("rama", "main")
    if os.path.isdir(os.path.join(DIR_REPO, ".git")):
        r = _git("remote", "get-url", "origin")
        if r.returncode == 0 and r.stdout.strip() == url:
            _git("fetch", "origin")
            if _git("rev-parse", "--verify", "--quiet", f"origin/{rama}").returncode == 0:
                _git("checkout", "-f", "-B", rama, f"origin/{rama}")
            _git("clean", "-fdq")
            return True
    shutil.rmtree(DIR_REPO, ignore_errors=True)
    print("Descargando el repositorio de GitHub...")
    r = _git("clone", url, DIR_REPO, cwd=DIR_SCRIPT, capturar=False)
    if r.returncode != 0:
        print("ERROR al descargar el repositorio.", _salida(r))
        return False
    if _git("rev-parse", "--verify", "HEAD").returncode != 0:
        _git("symbolic-ref", "HEAD", f"refs/heads/{rama}")
    usuario = _partes_repo(url)[0] or "calendario"
    _git("config", "user.name", "Calendario (configuración)")
    _git("config", "user.email", f"{usuario}@users.noreply.github.com")
    _git("config", "core.autocrlf", "false")
    return True


# ═════════════════════════════════════════════════════════════════════════════

def _abrir(ruta):
    try:
        if sys.platform.startswith("win"):
            os.startfile(ruta)
        else:
            import webbrowser
            webbrowser.open("file://" + os.path.abspath(ruta))
    except Exception as e:
        print(f"No se pudo abrir {ruta}: {e}")


def main():
    global _COLOR
    ap = argparse.ArgumentParser(description="Publica calendarios de Outlook (.ics) como página web estilo Outlook.")
    ap.add_argument("--configurar", action="store_true", help="calendarios, colores, tipos y opciones")
    ap.add_argument("--publicar", action="store_true", help="enviar la configuración a GitHub")
    ap.add_argument("--rehacer-github", action="store_true", help="volver a preparar la publicación desde cero")
    ap.add_argument("--paleta", action="store_true", help="ver la paleta de colores")
    ap.add_argument("--secreto", action="store_true", help="volver a copiar el secreto con las direcciones")
    ap.add_argument("--abrir", action="store_true", help="abrir la vista previa al terminar")
    ap.add_argument("--abrir-web", action="store_true", help="abrir la página publicada")
    ap.add_argument("--ci", action="store_true", help="modo GitHub Actions")
    ap.add_argument("--config", default=CONFIG_DEFECTO, help="archivo de configuración local")
    args = ap.parse_args()
    _COLOR = _color_consola() and not args.ci

    if args.ci:
        return modo_ci()
    if args.paleta:
        return mostrar_paleta()
    if args.secreto:
        return volver_a_pegar_secreto(args.config)
    if args.abrir_web:
        cfg = cargar_config(args.config) or {}
        web = (cfg.get("github") or {}).get("web")
        if web:
            print(web)
            _abrir_web(web)
        else:
            print("La publicación en GitHub no está preparada todavía.")
        return
    if args.publicar or args.rehacer_github:
        ok = publicar(args.config, rehacer=args.rehacer_github)
        sys.exit(0 if ok else 1)
    if args.configurar or not os.path.exists(args.config):
        if not sys.stdin.isatty() and not args.configurar:
            sys.exit("No existe la configuración. Ejecuta primero:  python calendario.py --configurar")
        if not configurar(args.config):
            return
        args.abrir = True
    cfg = cargar_config(args.config)
    ruta = generar_local(cfg)
    if args.abrir:
        _abrir(ruta)


_COLOR = False


# Plantilla de la página (HTML, CSS y JavaScript en un solo archivo)
PLANTILLA = r'''<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="only light">
<meta name="theme-color" content="#FFFFFF">
<meta name="generator" content="calendario.py __VERSION__">
<title>__TITULO__</title>
<style>
:root{
  /* Estética Outlook: cromo gris cálido, azul de marca, bloques con barra de color */
  --bg:#FAF9F8; --surface:#FFFFFF; --line:#EDEBE9; --line-strong:#D2D0CE;
  --text:#242424; --muted:#616161; --brand:#0F6CBD; --brand-soft:#EBF3FC;
  --exam:#C50F1F; --holiday:#F3F2F1;
  --font:"Segoe UI","Segoe UI Web (West European)",-apple-system,BlinkMacSystemFont,Roboto,"Helvetica Neue",Arial,sans-serif;
  --hora:56px;
  /* layout: barra superior · panel lateral (mini calendario + mis calendarios) · vista Semana/Mes/Agenda */
  color-scheme:only light;   /* siempre fondo claro, aunque el móvil esté en modo oscuro */
}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;background:var(--bg);color:var(--text);font:14px/1.35 var(--font);-webkit-text-size-adjust:100%}
button{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--brand);outline-offset:1px}

.top{display:flex;align-items:center;gap:10px 14px;flex-wrap:wrap;padding:10px 16px;background:var(--surface);border-bottom:1px solid var(--line)}
.marca{display:flex;align-items:center;gap:10px;min-width:0}
.logo{width:30px;height:30px;border-radius:6px;background:var(--brand);color:#fff;display:grid;place-items:center;flex:none}
.marca h1{font-size:16px;font-weight:600;margin:0;text-wrap:balance}
.marca p{margin:0;color:var(--muted);font-size:12px}
.nav{display:flex;align-items:center;gap:6px;margin-left:auto;flex-wrap:wrap}
.btn{border:1px solid var(--line-strong);background:var(--surface);border-radius:4px;padding:5px 12px;cursor:pointer;min-height:32px}
.btn:hover{background:var(--brand-soft)}
.btn.ico{padding:5px 9px;font-size:16px;line-height:1}
.btn:disabled{opacity:.4;cursor:default;background:var(--surface)}
.pasos{display:inline-flex;gap:6px}
.flecha{display:inline-flex;align-items:center;gap:6px;border:0;border-radius:6px;background:var(--brand);color:#fff;
  font-weight:600;padding:0 14px 0 10px;min-height:38px;cursor:pointer;box-shadow:0 1px 3px rgba(0,0,0,.18)}
.flecha.der{padding:0 10px 0 14px}
.flecha svg{width:20px;height:20px;flex:none}
.flecha:hover{background:#0C5AA0}
.flecha:active{transform:translateY(1px)}
.flecha:disabled{background:#C8C6C4;box-shadow:none;cursor:default}
body[data-vista="agenda"] .pasos{display:none}
.vistas{display:inline-flex;border:1px solid var(--line-strong);border-radius:4px;overflow:hidden}
.vistas button{border:0;background:var(--surface);padding:5px 12px;cursor:pointer;min-height:30px}
.vistas button+button{border-left:1px solid var(--line-strong)}
.vistas button[aria-pressed="true"]{background:var(--brand);color:#fff}
.rango{font-size:16px;font-weight:600;min-width:12em}
.chip{display:inline-block;font-size:12px;padding:2px 8px;border-radius:10px;font-weight:600;white-space:nowrap;
  background:color-mix(in srgb,var(--exam) 14%,var(--surface));color:var(--exam)}
.chip[hidden]{display:none}
.filtros-btn{display:none}

.app{display:grid;grid-template-columns:250px minmax(0,1fr);height:calc(100% - 58px)}
aside{border-right:1px solid var(--line);background:var(--surface);overflow:auto;padding:14px 14px 20px;display:flex;flex-direction:column;gap:18px}
main{overflow:auto;background:var(--surface)}

.mini-cab{display:flex;align-items:center;justify-content:space-between;margin-bottom:6px}
.mini-cab b{font-size:13px;font-weight:600;text-transform:capitalize}
.mini-cab .btn{min-height:26px;padding:2px 8px;border:0}
.mini{display:grid;grid-template-columns:repeat(7,1fr);gap:1px;text-align:center;font-size:12px;font-variant-numeric:tabular-nums}
.mini .dsem{color:var(--muted);font-size:11px;padding:2px 0}
.mini button{border:0;background:none;padding:4px 0;border-radius:4px;cursor:pointer;position:relative}
.mini button:hover{background:var(--brand-soft)}
.mini .fuera{color:var(--muted);opacity:.55}
.mini .finde{color:var(--muted)}
.mini .sel{background:var(--brand-soft)}
.mini .hoy{background:var(--brand);color:#fff;font-weight:700}
.mini .ev-dia::after{content:"";position:absolute;left:50%;bottom:1px;width:3px;height:3px;margin-left:-1.5px;border-radius:50%;background:var(--muted)}
.mini .hoy.ev-dia::after{background:#fff}

#listas{display:flex;flex-direction:column;gap:14px}
.bloque h2{font-size:12px;font-weight:600;color:var(--muted);margin:0 0 6px;text-transform:uppercase;letter-spacing:.04em}
.cal-item{display:flex;align-items:center;gap:8px;padding:5px 4px;border-radius:4px;cursor:pointer;user-select:none}
.cal-item:hover{background:var(--bg)}
.cal-item input{position:absolute;opacity:0;pointer-events:none}
.check{width:16px;height:16px;border-radius:3px;border:2px solid var(--c);flex:none;display:grid;place-items:center}
.cal-item input:checked+.check{background:var(--c)}
.cal-item input:checked+.check::after{content:"";width:8px;height:4px;border:2px solid #fff;border-top:0;border-right:0;transform:rotate(-45deg) translate(1px,-1px)}
.cal-item input:focus-visible+.check{outline:2px solid var(--brand);outline-offset:2px}
.cal-item .n{font-size:13px}
.seg{display:flex;border:1px solid var(--line-strong);border-radius:4px;overflow:hidden}
.seg button{flex:1;border:0;background:var(--surface);padding:5px 0;cursor:pointer;font-size:13px}
.seg button+button{border-left:1px solid var(--line-strong)}
.seg button[aria-pressed="true"]{background:var(--brand);color:#fff}
.info{font-size:12px;color:var(--muted);line-height:1.45}
.avisos{font-size:12px;color:var(--exam);line-height:1.45}

/* Semana */
.semana{min-width:0}
.cabdias,.todo-dia,.cuerpo{display:grid;grid-template-columns:56px repeat(var(--n),minmax(0,1fr))}
.cabdias{position:sticky;top:0;z-index:5;background:var(--surface);border-bottom:1px solid var(--line)}
.cabdia{padding:8px 8px 6px;border-left:1px solid var(--line)}
.cabdia .num{font-size:22px;font-weight:300;line-height:1}
.cabdia .dia{font-size:12px;color:var(--muted)}
.cabdia.hoy .num{color:var(--brand);font-weight:600}
.cabdia.hoy{box-shadow:inset 0 3px 0 var(--brand)}
.todo-dia{border-bottom:1px solid var(--line-strong)}
.todo-dia .celda{border-left:1px solid var(--line);padding:3px 4px;min-height:8px;display:flex;flex-direction:column;gap:2px}
.todo-dia .lbl{font-size:10px;color:var(--muted);padding:5px 6px 0;text-align:right}
.td{font-size:12px;padding:2px 6px;border-radius:3px;background:color-mix(in srgb,var(--c) 30%,var(--surface));border-left:3px solid var(--cb);font-weight:600;
  white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;text-align:left;border-top:0;border-right:0;border-bottom:0}
.horas div{height:var(--hora);font-size:11px;color:var(--muted);text-align:right;padding-right:8px;transform:translateY(-7px);font-variant-numeric:tabular-nums}
.col{position:relative;border-left:1px solid var(--line);background:
  repeating-linear-gradient(to bottom,var(--line) 0 1px,transparent 1px calc(var(--hora)/2),var(--line) calc(var(--hora)/2) calc(var(--hora)/2 + 1px),transparent calc(var(--hora)/2 + 1px) var(--hora))}
.col.festivo{background-color:var(--holiday)}
.col.hoy{background-color:color-mix(in srgb,var(--brand) 5%,var(--surface))}
.ahora{position:absolute;left:-1px;right:0;height:2px;background:#C50F1F;z-index:3}
.ahora::before{content:"";position:absolute;left:-5px;top:-4px;width:10px;height:10px;border-radius:50%;background:#C50F1F}
.ev{position:absolute;border-radius:4px;padding:3px 6px 3px 8px;overflow:hidden;cursor:pointer;
  background:color-mix(in srgb,var(--c) 30%,var(--surface));border:0;border-left:4px solid var(--cb);color:var(--text);
  font-size:12px;line-height:1.3;text-align:left;z-index:2}
.ev:hover{filter:brightness(.97);z-index:4}
.ev .t{font-weight:600;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.ev .h,.ev .a{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:var(--muted)}
.tag{display:inline-block;font-size:10.5px;font-weight:700;padding:0 6px;border-radius:8px;background:var(--cb);color:#fff;margin:0 0 2px;white-space:nowrap}
.practica{border:1.5px solid var(--cb);border-left-width:4px;background:color-mix(in srgb,var(--c) 22%,var(--surface))}
.practica .t{font-weight:700}
.examen{border:2px solid var(--exam);border-left-width:5px;background:color-mix(in srgb,var(--c) 35%,var(--surface))}
.examen .t{font-weight:800}
.examen .tag{background:var(--exam);letter-spacing:.03em}

/* Mes */
.mes{min-width:560px}
.mes .dsem{display:grid;grid-template-columns:repeat(var(--n),minmax(0,1fr));font-size:12px;color:var(--muted);font-weight:600;padding:6px 0 4px 8px;border-bottom:1px solid var(--line)}
.mes .dsem .c{display:none}
.mes .fila{display:grid;grid-template-columns:repeat(var(--n),minmax(0,1fr));border-bottom:1px solid var(--line)}
.mes .dia{min-height:112px;border-left:1px solid var(--line);padding:4px;display:flex;flex-direction:column;gap:2px;cursor:pointer;min-width:0}
.mes .dia:first-child{border-left:0}
.mes .dia:hover{background:var(--bg)}
.mes .dia.fuera{background:var(--bg)}
.mes .dia.fuera .num{color:var(--muted)}
.mes .dia.festivo{background:var(--holiday)}
.mes .num{font-size:12px;font-weight:600;padding:2px 4px}
.mes .dia.hoy .num span{background:var(--brand);color:#fff;border-radius:10px;padding:1px 7px}
.mc{font-size:11.5px;line-height:1.35;padding:1px 5px;border-radius:3px;border-left:3px solid var(--cb);background:color-mix(in srgb,var(--c) 26%,var(--surface));
  white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.mc b{font-weight:600}
.mc.practica{border:1px solid var(--cb);border-left-width:3px}
.mc.examen{border:1.5px solid var(--exam);border-left-width:3px;font-weight:700}
.mas{font-size:11.5px;color:var(--muted);font-weight:600;padding:0 5px}

/* Agenda */
.agenda{max-width:820px;padding:4px 18px 24px}
.ag-dia{margin:0 0 10px}
.ag-dia h3{font-size:15px;margin:0 0 4px;padding:10px 0 5px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--surface);z-index:2}
.ag-dia.hoy h3{color:var(--brand)}
.ag-dia.hoy h3::after{content:" · hoy";font-weight:400}
.ag-item{display:grid;grid-template-columns:12px 7.2em minmax(0,1fr);gap:2px 10px;align-items:baseline;padding:6px 4px;border:0;background:none;width:100%;text-align:left;cursor:pointer;border-radius:4px}
.ag-item:hover{background:var(--bg)}
.ag-item .sw{width:11px;height:11px;border-radius:3px;background:var(--cb);align-self:center}
.ag-item.examen .sw{outline:2px solid var(--exam);outline-offset:1px}
.ag-item .hr{font-variant-numeric:tabular-nums;font-size:13px;white-space:nowrap}
.ag-item .tt{font-weight:600}
.ag-item .tt .tag{margin:0 6px 0 0;vertical-align:1px}
.ag-item .meta{display:block;font-weight:400;color:var(--muted);font-size:12.5px}
.vacio{color:var(--muted);padding:24px 18px}

.detalle{position:fixed;inset:0;background:rgba(0,0,0,.25);display:grid;place-items:center;z-index:20;padding:16px}
.detalle[hidden]{display:none}
.tarjeta{background:var(--surface);border-radius:8px;box-shadow:0 8px 28px rgba(0,0,0,.25);max-width:400px;width:100%;overflow:hidden}
.tarjeta .franja{height:6px;background:var(--cb)}
.tarjeta .dentro{padding:14px 18px 16px}
.tarjeta h3{margin:0 0 8px;font-size:17px;font-weight:600;text-wrap:balance}
.tarjeta dl{display:grid;grid-template-columns:auto 1fr;gap:4px 12px;margin:0 0 14px;font-size:13px}
.tarjeta dt{color:var(--muted)}
.tarjeta dd{margin:0}

.tabs{display:none}
/* Pantallas estrechas o bajas (tablet, móvil en horizontal): el panel de calendarios se pliega
   bajo el botón «Calendarios» y la semana ocupa todo el ancho, de lunes a viernes */
@media (max-width:1000px),(max-height:560px){
  .app{grid-template-columns:1fr;height:auto}
  main{overflow:visible}
  aside{display:none;border-right:0;border-bottom:1px solid var(--line)}
  body.ver-panel aside{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:18px 28px}
  .filtros-btn{display:inline-block}
  .semana,.mes{min-width:0}
  .cabdias,.todo-dia,.cuerpo{grid-template-columns:44px repeat(var(--n),minmax(0,1fr))}
  .cabdia{padding:6px 6px 4px}
  .ev{padding:2px 4px 2px 6px}
}
@media (max-height:560px) and (orientation:landscape){
  .top{padding:6px 12px}
  .marca p{display:none}
  .marca h1{font-size:15px}
  .flecha .txt{display:none}
  .flecha,.flecha.der{padding:0;width:48px;min-height:38px;justify-content:center}
  .flecha svg{width:24px;height:24px}
  .rango{font-size:15px}
  .cabdia{display:flex;align-items:baseline;gap:6px}
  .cabdia .num{font-size:18px}
  .rango{min-width:0}
}
/* Móvil en vertical: un día cada vez, con pestañas L–V */
@media (max-width:760px) and (orientation:portrait){
  .nav{margin-left:0;width:100%}
  .rango{min-width:0;width:100%;order:-1;font-size:16px}
  .chip{order:-1}
  .filtros-btn{margin-left:auto}
  .flecha .txt{display:none}
  .flecha,.flecha.der{padding:0;width:46px;min-height:40px;justify-content:center}
  .flecha svg{width:24px;height:24px}
  body[data-vista="semana"] .tabs{display:grid;grid-template-columns:44px repeat(var(--n),1fr) 44px;gap:4px;padding:8px 8px;background:var(--surface);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:6}
  .tabs .flecha,.tabs .flecha:hover{background:var(--brand);color:#fff;width:44px;min-height:44px;align-self:center;border-radius:8px;display:inline-flex;justify-content:center;padding:0}
  .tabs .flecha:disabled{background:#C8C6C4}
  body[data-vista="semana"] .top .pasos{display:none}   /* en Semana las flechas van junto a los días */
  .tabs button{border:0;background:none;border-radius:6px;padding:4px 0;cursor:pointer}
  .tabs .d{display:block;font-size:11px;color:var(--muted)}
  .tabs .n{display:block;font-size:18px;font-weight:300}
  .tabs button[aria-pressed="true"]{background:var(--brand);color:#fff}
  .tabs button[aria-pressed="true"] .d{color:#fff}
  .tabs button.hoy:not([aria-pressed="true"]) .n{color:var(--brand);font-weight:600}
  .semana .cabdias{display:none}
  .cabdias,.todo-dia,.cuerpo{grid-template-columns:56px repeat(var(--n),minmax(0,1fr))}
  .semana{--n:1!important}
  .semana .col:not(.activa),.semana .todo-dia .celda:not(.activa){display:none}
  .ev{font-size:13px}
  .mes .dsem .l{display:none}.mes .dsem .c{display:inline}
  .mes .dia{min-height:62px;padding:2px}
  .mc{font-size:0;height:6px;padding:0;border:0;background:var(--cb);border-radius:3px}
  .mc.examen{background:var(--exam)}
  .mas{font-size:10px;padding:0 2px}
  .agenda{padding:0 12px 20px}
  .ag-item{grid-template-columns:10px 6.2em minmax(0,1fr);gap:2px 8px}
  .ag-item .hr{font-size:12px}
}
@media print{.top .nav,aside,.tabs{display:none!important}.app{display:block;height:auto}main{overflow:visible}}
@media (prefers-reduced-motion:reduce){*{scroll-behavior:auto!important}}
</style>
</head>
<body data-vista="semana">
<header class="top">
  <div class="marca">
    <div class="logo" aria-hidden="true"><svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="3" y="5" width="18" height="16" rx="2"/><path d="M3 10h18M8 3v4M16 3v4"/></svg></div>
    <div><h1 id="titulo"></h1><p id="subtitulo"></p></div>
  </div>
  <div class="nav">
    <div class="vistas" role="group" aria-label="Vista">
      <button data-vista="semana" aria-pressed="true">Semana</button><button data-vista="mes" aria-pressed="false">Mes</button><button data-vista="agenda" aria-pressed="false">Agenda</button>
    </div>
    <button class="btn" id="hoy">Hoy</button>
    <div class="pasos">
      <button class="flecha izq" id="ant" aria-label="Semana anterior"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 5l-7 7 7 7"/></svg><span class="txt">Semana anterior</span></button>
      <button class="flecha der" id="sig" aria-label="Semana siguiente"><span class="txt">Semana siguiente</span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 5l7 7-7 7"/></svg></button>
    </div>
    <span class="rango" id="rango"></span>
    <span class="chip" id="chip" hidden>Exámenes esta semana</span>
    <button class="btn filtros-btn" id="panel" aria-expanded="false">Calendarios</button>
  </div>
</header>
<div class="app">
  <aside>
    <div>
      <div class="mini-cab"><button class="btn" id="mant" aria-label="Mes anterior">&#8249;</button><b id="mtit"></b><button class="btn" id="msig" aria-label="Mes siguiente">&#8250;</button></div>
      <div class="mini" id="mini"></div>
    </div>
    <div id="listas"></div>
    <div class="bloque" id="bloque-grupos" hidden><h2>Grupo</h2><div class="seg" id="grupos"></div></div>
    <div class="avisos" id="avisos" hidden></div>
    <div class="info" id="info"></div>
  </aside>
  <main>
    <div class="tabs" id="tabs"></div>
    <div id="vista"></div>
  </main>
</div>
<div class="detalle" id="detalle" hidden><div class="tarjeta" role="dialog" aria-modal="true" aria-labelledby="dt-tit">
  <div class="franja" id="dt-franja"></div>
  <div class="dentro"><h3 id="dt-tit"></h3><dl id="dt-dl"></dl><button class="btn" id="dt-cerrar">Cerrar</button></div>
</div></div>
<script>
const D = __DATOS__;
(function(){
  "use strict";
  const $=s=>document.querySelector(s);
  const MESES=["enero","febrero","marzo","abril","mayo","junio","julio","agosto","septiembre","octubre","noviembre","diciembre"];
  const DIAS=["Lunes","Martes","Miércoles","Jueves","Viernes","Sábado","Domingo"], DC=["L","M","X","J","V","S","D"];
  const N=D.dias, CAL={}; D.calendarios.forEach(c=>CAL[c.clave]=c);
  const TIPOS={teoria:"Clase",practica:"Práctica",examen:"Examen",otro:"Evento"};
  const mem={get(k){try{return JSON.parse(localStorage.getItem("calfmed."+k))}catch(e){return null}},
             set(k,v){try{localStorage.setItem("calfmed."+k,JSON.stringify(v))}catch(e){}}};
  const pad=n=>String(n).padStart(2,"0");
  const iso=d=>d.getFullYear()+"-"+pad(d.getMonth()+1)+"-"+pad(d.getDate());
  const aFecha=s=>{const p=s.slice(0,10).split("-").map(Number);return new Date(p[0],p[1]-1,p[2])};
  const masDias=(d,n)=>new Date(d.getFullYear(),d.getMonth(),d.getDate()+n);
  const lunesDe=d=>masDias(d,-((d.getDay()+6)%7));
  const hnum=s=>{const t=s.slice(11,16).split(":").map(Number);return t[0]+t[1]/60};
  const hora=s=>s.slice(11,16);
  const movil=()=>window.matchMedia("(max-width:760px) and (orientation:portrait)").matches;
  const estrecho=()=>window.matchMedia("(max-width:1000px),(max-height:560px)").matches;
  const HOYD=new Date(), HOY=iso(HOYD);
  const R0=aFecha(D.rango[0]), R1=aFecha(D.rango[1]);
  const oscuro=hex=>{const n=parseInt(hex.slice(1),16);const f=.62;return "#"+[n>>16,n>>8&255,n&255].map(v=>Math.round(v*f).toString(16).padStart(2,"0")).join("")};

  // ── eventos ──
  const EV=D.eventos.map(e=>{
    e.d0=e.i.slice(0,10);
    if(e.td) e.d1=iso(masDias(aFecha(e.f),-1));
    else { e.d1=e.f.slice(0,10); if(e.f.slice(11,16)==="00:00"&&e.d1>e.d0) e.d1=iso(masDias(aFecha(e.f),-1)); }
    if(e.d1<e.d0) e.d1=e.d0;
    e.color=(e.a&&CAL[e.a])?CAL[e.a].color:CAL[e.c].color;
    e.arriba=e.td||e.d1>e.d0;                      // fila de "todo el día"
    e.festivo=e.td&&/festivo|no lectivo/i.test(e.t);
    return e;
  });
  const conEventos=new Set(); EV.forEach(e=>{for(let d=aFecha(e.d0);iso(d)<=e.d1;d=masDias(d,1)) conEventos.add(iso(d))});
  const GRUPOS=[...new Set(EV.flatMap(e=>e.g))].sort((a,b)=>a.localeCompare(b,"es",{numeric:true}));
  let H0=24,H1=0; EV.filter(e=>!e.arriba).forEach(e=>{H0=Math.min(H0,Math.floor(hnum(e.i)));H1=Math.max(H1,Math.ceil(hnum(e.f)||24))});
  if(H0>H1){H0=8;H1=20} H0=Math.min(H0,8); H1=Math.max(H1,H0+9,20); H1=Math.min(H1,24);

  // ── estado ──
  const ocultos=new Set(mem.get("ocultos")||[]);
  let grupo=mem.get("grupo"); if(!GRUPOS.includes(grupo)) grupo="todos";
  let vista=mem.get("vista")||"semana"; if(!["semana","mes","agenda"].includes(vista)) vista="semana";
  let cursor, diaMovil=0, miniMes, verPasados=false;
  const visible=e=>!ocultos.has(e.c)&&(grupo==="todos"||!e.g.length||e.g.includes(grupo));
  const delDia=f=>EV.filter(e=>e.d0<=f&&e.d1>=f&&visible(e));
  const textoTag=e=>e.tipo==="practica"?("Práctica"+(e.g.length?" · "+e.g.join(" y "):"")):e.tipo==="examen"?(/parcial/i.test(e.t)?"EXAMEN PARCIAL":"EXAMEN"):"";
  // Título sin lo que ya dice la etiqueta ("Práctica ... · G1", "EXAMEN PARCIAL · ...")
  const corto=e=>{if(e.tipo!=="practica"&&e.tipo!=="examen") return e.t;
    let t=e.t.replace(/^\s*(pr[aá]cticas?|examen(es)?(\s+parcial(es)?)?|parcial)\b\s*[:·\-–]?\s*/i,"");
    if(e.tipo==="practica") t=t.replace(/\s*[·\-–(,]?\s*G\s?\d{1,2}(\s*(y|e|,|\/)\s*G?\s?\d{1,2})?\)?\s*$/i,"");
    return t.trim()||e.t};
  function estilo(el,e){el.style.setProperty("--c",e.color);el.style.setProperty("--cb",oscuro(e.color))}

  // ── cabecera y panel ──
  $("#titulo").textContent=D.titulo; document.title=D.titulo;
  $("#subtitulo").textContent=D.subtitulo||""; if(!D.subtitulo) $("#subtitulo").hidden=true;
  $("#info").textContent="Actualizado: "+D.actualizado+". Pulsa un evento para ver los detalles.";
  if(D.avisos&&D.avisos.length){$("#avisos").hidden=false;$("#avisos").textContent=D.avisos.join(" · ")}
  document.documentElement.style.setProperty("--n",N);
  const ENCAB={asignatura:"Asignaturas",practicas:"Prácticas",examenes:"Exámenes",otros:"Otros"};
  for(const tipo of Object.keys(ENCAB)){
    const cs=D.calendarios.filter(c=>c.tipo===tipo); if(!cs.length) continue;
    const b=document.createElement("div"); b.className="bloque"; b.innerHTML=`<h2>${ENCAB[tipo]}</h2>`;
    for(const c of cs){
      const l=document.createElement("label"); l.className="cal-item"; l.style.setProperty("--c",oscuro(c.color));
      l.innerHTML=`<input type="checkbox" id="cal-${c.clave}"><span class="check"></span><span class="n"></span>`;
      l.querySelector(".n").textContent=c.nombre;
      const inp=l.querySelector("input"); inp.checked=!ocultos.has(c.clave);
      inp.onchange=()=>{inp.checked?ocultos.delete(c.clave):ocultos.add(c.clave);mem.set("ocultos",[...ocultos]);pintar()};
      b.append(l);
    }
    $("#listas").append(b);
  }
  if(GRUPOS.length){
    $("#bloque-grupos").hidden=false;
    $("#grupos").innerHTML=["todos",...GRUPOS].map(g=>`<button data-g="${g}" aria-pressed="${g===grupo}">${g==="todos"?"Todos":g}</button>`).join("");
    $("#grupos").querySelectorAll("button").forEach(b=>b.onclick=()=>{grupo=b.dataset.g;mem.set("grupo",grupo);
      $("#grupos").querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",x===b));pintar()});
  }

  // ── detalle ──
  function detalle(e){
    $("#dt-franja").style.setProperty("--cb",oscuro(e.color));
    $("#dt-tit").textContent=e.t;
    const d0=aFecha(e.d0), d1=aFecha(e.d1);
    const fmt=d=>`${DIAS[(d.getDay()+6)%7].toLowerCase()} ${d.getDate()} de ${MESES[d.getMonth()]}`;
    const filas=[["Calendario",CAL[e.c].nombre],["Tipo",TIPOS[e.tipo]],["Fecha",e.d1>e.d0?`del ${fmt(d0)} al ${fmt(d1)}`:fmt(d0)],
      ["Hora",e.td?"Todo el día":`${hora(e.i)} – ${hora(e.f)}`],["Lugar",e.u],["Grupo",e.g.join(" y ")]].filter(x=>x[1]);
    const dl=$("#dt-dl"); dl.innerHTML="";
    filas.forEach(([k,v])=>{const dt=document.createElement("dt"),dd=document.createElement("dd");dt.textContent=k;dd.textContent=v;dl.append(dt,dd)});
    $("#detalle").hidden=false; $("#dt-cerrar").focus();
  }
  $("#dt-cerrar").onclick=()=>$("#detalle").hidden=true;
  $("#detalle").addEventListener("click",e=>{if(e.target.id==="detalle")$("#detalle").hidden=true});
  document.addEventListener("keydown",e=>{if(e.key==="Escape")$("#detalle").hidden=true});

  function boton(cls,e,html){const b=document.createElement("button");b.className=cls+" "+e.tipo;estilo(b,e);b.innerHTML=html;b.onclick=ev=>{ev.stopPropagation();detalle(e)};return b}

  // ── vista Semana ──
  function columnas(evs){
    evs.sort((a,b)=>hnum(a.i)-hnum(b.i)||hnum(b.f)-hnum(a.f));
    let grupoAct=[],fin=-1; const grupos=[];
    for(const e of evs){if(hnum(e.i)>=fin&&grupoAct.length){grupos.push(grupoAct);grupoAct=[]}grupoAct.push(e);fin=Math.max(fin,hnum(e.f)||24)}
    if(grupoAct.length) grupos.push(grupoAct);
    for(const g of grupos){const fines=[];for(const e of g){let c=fines.findIndex(f=>f<=hnum(e.i));if(c<0){c=fines.length;fines.push(0)}fines[c]=hnum(e.f)||24;e._c=c}g.forEach(e=>e._n=fines.length)}
  }
  function pintarSemana(){
    const l=lunesDe(cursor), dias=[...Array(N).keys()].map(i=>masDias(l,i));
    const v=dias[N-1];
    $("#rango").textContent=l.getMonth()===v.getMonth()?`${l.getDate()}–${v.getDate()} de ${mesTxt(v.getMonth())} de ${v.getFullYear()}`
      :`${l.getDate()} de ${mesTxt(l.getMonth())} – ${v.getDate()} de ${mesTxt(v.getMonth())}`+(l.getFullYear()!==v.getFullYear()?` de ${v.getFullYear()}`:"");
    $("#chip").hidden=!dias.some(d=>delDia(iso(d)).some(e=>e.tipo==="examen"));
    const fl=(id,d)=>`<button class="flecha" data-paso="${id}" aria-label="Semana ${id==="ant"?"anterior":"siguiente"}"${$("#"+id).disabled?" disabled":""}><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="${d}"/></svg></button>`;
    $("#tabs").innerHTML=fl("ant","M15 5l-7 7 7 7")+dias.map((d,i)=>`<button aria-pressed="${i===diaMovil}" class="${iso(d)===HOY?"hoy":""}" data-i="${i}"><span class="d">${DC[(d.getDay()+6)%7]}</span><span class="n">${d.getDate()}</span></button>`).join("")+fl("sig","M9 5l7 7-7 7");
    $("#tabs").querySelectorAll("[data-paso]").forEach(b=>b.onclick=()=>$("#"+b.dataset.paso).click());
    $("#tabs").querySelectorAll("button[data-i]").forEach(b=>b.onclick=()=>{diaMovil=+b.dataset.i;cursor=dias[diaMovil];pintar(true)});
    let h=`<div class="semana"><div class="cabdias"><div></div>`;
    dias.forEach(d=>h+=`<div class="cabdia${iso(d)===HOY?" hoy":""}"><div class="num">${d.getDate()}</div><div class="dia">${DIAS[(d.getDay()+6)%7]}</div></div>`);
    h+=`</div><div class="todo-dia"><div class="lbl">Todo el día</div>`;
    dias.forEach((d,i)=>h+=`<div class="celda${i===diaMovil?" activa":""}" data-f="${iso(d)}"></div>`);
    h+=`</div><div class="cuerpo"><div class="horas">`;
    for(let x=H0;x<H1;x++) h+=`<div>${x===H0?"":x+":00"}</div>`;
    h+=`</div>`;
    dias.forEach((d,i)=>{const f=iso(d),fest=EV.some(e=>e.festivo&&visible(e)&&e.d0<=f&&e.d1>=f);
      h+=`<div class="col${fest?" festivo":""}${f===HOY?" hoy":""}${i===diaMovil?" activa":""}" style="height:calc(var(--hora)*${H1-H0})" data-f="${f}"></div>`});
    $("#vista").innerHTML=h+"</div></div>";
    dias.forEach(d=>{
      const f=iso(d), evs=delDia(f);
      const arriba=document.querySelector(`.todo-dia .celda[data-f="${f}"]`);
      evs.filter(e=>e.arriba).forEach(e=>{const t=e.td?"":hora(e.i)+" ";const b=boton("td",e,"");b.textContent=t+e.t;arriba.append(b)});
      const col=document.querySelector(`.col[data-f="${f}"]`), cuerpo=evs.filter(e=>!e.arriba);
      columnas(cuerpo);
      for(const e of cuerpo){
        const tag=textoTag(e);
        const b=boton("ev",e,(tag?`<span class="tag"></span>`:"")+`<span class="t"></span><span class="h">${hora(e.i)}–${hora(e.f)}</span><span class="a"></span>`);
        if(tag) b.querySelector(".tag").textContent=tag;
        b.querySelector(".t").textContent=corto(e); b.querySelector(".a").textContent=e.u||"";
        const ini=Math.max(hnum(e.i),H0), fin=Math.min(hnum(e.f)||24,H1);
        b.style.top=`calc(var(--hora)*${ini-H0} + 1px)`; b.style.height=`calc(var(--hora)*${Math.max(fin-ini,.4)} - 3px)`;
        b.style.left=`calc(${100*e._c/e._n}% + 2px)`; b.style.width=`calc(${100/e._n}% - 5px)`;
        b.setAttribute("aria-label",`${e.t}, ${hora(e.i)} a ${hora(e.f)}${e.u?", "+e.u:""}`);
        col.append(b);
      }
      if(f===HOY){const a=HOYD.getHours()+HOYD.getMinutes()/60;if(a>=H0&&a<=H1){const x=document.createElement("div");x.className="ahora";x.style.top=`calc(var(--hora)*${a-H0})`;col.append(x)}}
    });
  }

  // ── vista Mes ──
  function pintarMes(){
    const y=cursor.getFullYear(), m=cursor.getMonth(), p=new Date(y,m,1), ult=new Date(y,m+1,0);
    $("#rango").textContent=`${MESES[m]} de ${y}`; $("#chip").hidden=true;
    let h=`<div class="mes"><div class="dsem">${[...Array(N).keys()].map(i=>`<div><span class="l">${DIAS[i]}</span><span class="c">${DC[i]}</span></div>`).join("")}</div>`;
    for(let l=lunesDe(p);l<=ult;l=masDias(l,7)){
      const dias=[...Array(N).keys()].map(i=>masDias(l,i));
      if(!dias.some(d=>d.getMonth()===m)) continue;
      h+=`<div class="fila">`+dias.map(d=>{const f=iso(d);const fest=EV.some(e=>e.festivo&&visible(e)&&e.d0<=f&&e.d1>=f);
        return `<div class="dia${d.getMonth()!==m?" fuera":""}${f===HOY?" hoy":""}${fest?" festivo":""}" data-f="${f}"><div class="num"><span>${d.getDate()===1?d.getDate()+" "+MESES[d.getMonth()].slice(0,3):d.getDate()}</span></div></div>`}).join("")+`</div>`;
    }
    $("#vista").innerHTML=h+"</div>";
    const cab=movil()?6:4;
    document.querySelectorAll(".mes .dia").forEach(c=>{
      const evs=delDia(c.dataset.f).sort((a,b)=>(b.arriba-a.arriba)||a.i.localeCompare(b.i));
      evs.slice(0,cab).forEach(e=>{const b=document.createElement("div");b.className="mc "+e.tipo;estilo(b,e);
        b.innerHTML=e.arriba?"":`<b>${hora(e.i)}</b> `; b.append(document.createTextNode(e.t));b.title=e.t;c.append(b)});
      if(evs.length>cab){const x=document.createElement("div");x.className="mas";x.textContent=`+${evs.length-cab} más`;c.append(x)}
      c.onclick=()=>{cursor=aFecha(c.dataset.f);diaMovil=Math.min((cursor.getDay()+6)%7,N-1);ponerVista("semana")};
    });
  }

  // ── vista Agenda ──
  function pintarAgenda(){
    $("#rango").textContent="Agenda"; $("#chip").hidden=true;
    const dias=[...conEventos].sort(); const cont=document.createElement("div"); cont.className="agenda";
    let pasados=0;
    for(const f of dias){
      const d=aFecha(f); if((d.getDay()+6)%7>=N) continue;
      const evs=delDia(f).sort((a,b)=>(b.arriba-a.arriba)||a.i.localeCompare(b.i)); if(!evs.length) continue;
      if(f<HOY&&!verPasados){pasados++;continue}
      const sec=document.createElement("section"); sec.className="ag-dia"+(f===HOY?" hoy":"");
      sec.innerHTML=`<h3>${DIAS[(d.getDay()+6)%7]} ${d.getDate()} de ${MESES[d.getMonth()]}${d.getFullYear()!==HOYD.getFullYear()?" de "+d.getFullYear():""}</h3>`;
      for(const e of evs){
        const tag=textoTag(e);
        const b=boton("ag-item",e,`<span class="sw"></span><span class="hr">${e.td?"Todo el día":hora(e.i)+"–"+hora(e.f)}</span><span class="tt">${tag?'<span class="tag"></span>':""}<span class="x"></span><span class="meta"></span></span>`);
        if(tag) b.querySelector(".tag").textContent=tag;
        b.querySelector(".x").textContent=corto(e); b.querySelector(".meta").textContent=[e.u,CAL[e.c].nombre].filter(Boolean).join(" · ");
        sec.append(b);
      }
      cont.append(sec);
    }
    if(pasados){const b=document.createElement("button");b.className="btn";b.style.margin="12px 0 4px";b.textContent=`Ver días anteriores (${pasados})`;b.onclick=()=>{verPasados=true;pintar()};cont.prepend(b)}
    if(!cont.querySelector(".ag-dia")){const p=document.createElement("p");p.className="vacio";p.textContent="No hay eventos próximos con los calendarios seleccionados.";cont.append(p)}
    $("#vista").innerHTML=""; $("#vista").append(cont);
  }

  // ── mini calendario ──
  function pintarMini(){
    const [y,m]=miniMes, p=new Date(y,m,1), ini=lunesDe(p);
    $("#mtit").textContent=`${MESES[m]} ${y}`;
    const ls=lunesDe(cursor);
    let h=DC.map(d=>`<div class="dsem">${d}</div>`).join("");
    for(let i=0;i<42;i++){const d=masDias(ini,i); if(i>=35&&d.getMonth()!==m) break;
      const f=iso(d),w=(d.getDay()+6)%7;
      const sel=vista==="semana"?(d>=ls&&d<masDias(ls,7)):(vista==="mes"&&d.getMonth()===cursor.getMonth()&&d.getFullYear()===cursor.getFullYear());
      h+=`<button class="${[d.getMonth()!==m?"fuera":"",w>4?"finde":"",f===HOY?"hoy":"",conEventos.has(f)?"ev-dia":"",sel?"sel":""].join(" ")}" data-f="${f}" aria-label="${d.getDate()} de ${MESES[d.getMonth()]}">${d.getDate()}</button>`}
    $("#mini").innerHTML=h;
    $("#mini").querySelectorAll("button").forEach(b=>b.onclick=()=>{cursor=aFecha(b.dataset.f);diaMovil=Math.min((cursor.getDay()+6)%7,N-1);
      document.body.classList.remove("ver-panel");$("#panel").setAttribute("aria-expanded","false");ponerVista(vista==="agenda"?"semana":vista)});
    $("#mant").disabled=new Date(y,m,1)<=new Date(R0.getFullYear(),R0.getMonth(),1);
    $("#msig").disabled=new Date(y,m,1)>=new Date(R1.getFullYear(),R1.getMonth(),1);
  }
  $("#mant").onclick=()=>{miniMes=[miniMes[0],miniMes[1]-1];if(miniMes[1]<0)miniMes=[miniMes[0]-1,11];pintarMini()};
  $("#msig").onclick=()=>{miniMes=[miniMes[0],miniMes[1]+1];if(miniMes[1]>11)miniMes=[miniMes[0]+1,0];pintarMini()};

  // ── navegación ──
  const mesTxt=m=>estrecho()?MESES[m].slice(0,3):MESES[m];
  function limitar(d){if(d<R0)d=new Date(R0);if(d>R1)d=new Date(R1);let w=(d.getDay()+6)%7;if(w>=N)d=masDias(d,7-w);if(d>R1)d=masDias(d,-7);return d}
  function pintar(desplazar){
    document.body.dataset.vista=vista;
    document.querySelectorAll(".vistas button").forEach(b=>b.setAttribute("aria-pressed",b.dataset.vista===vista));
    const ant=$("#ant"),sig=$("#sig"), u=vista==="mes"?["Mes anterior","Mes siguiente"]:["Semana anterior","Semana siguiente"];
    ant.querySelector(".txt").textContent=u[0]; ant.setAttribute("aria-label",u[0]);
    sig.querySelector(".txt").textContent=u[1]; sig.setAttribute("aria-label",u[1]);
    if(vista==="semana"){ant.disabled=lunesDe(cursor)<=R0;sig.disabled=masDias(lunesDe(cursor),7)>R1;pintarSemana()}
    else if(vista==="mes"){pintarMes();ant.disabled=new Date(cursor.getFullYear(),cursor.getMonth(),1)<=R0;sig.disabled=new Date(cursor.getFullYear(),cursor.getMonth()+1,1)>R1}
    else{pintarAgenda();ant.disabled=sig.disabled=true}
    if(!miniMes||desplazar!==false) miniMes=[cursor.getFullYear(),cursor.getMonth()];
    pintarMini();
    if(movil()&&vista==="semana"&&desplazar){const c=document.querySelector(".col.activa");const p=c&&[...c.querySelectorAll(".ev")].sort((a,b)=>a.offsetTop-b.offsetTop)[0];
      if(p) window.scrollTo({top:p.getBoundingClientRect().top+window.scrollY-150})}
  }
  function ponerVista(v){vista=v;mem.set("vista",v);pintar(true)}
  document.querySelectorAll(".vistas button").forEach(b=>b.onclick=()=>ponerVista(b.dataset.vista));
  $("#hoy").onclick=()=>{cursor=limitar(new Date(HOYD));diaMovil=Math.min((cursor.getDay()+6)%7,N-1);verPasados=false;pintar(true);if(vista==="agenda")window.scrollTo(0,0)};
  $("#ant").onclick=()=>{cursor=vista==="mes"?new Date(cursor.getFullYear(),cursor.getMonth()-1,1):masDias(lunesDe(cursor),-7);if(vista==="mes")cursor=limitar(cursor);diaMovil=0;pintar(true)};
  $("#sig").onclick=()=>{cursor=vista==="mes"?new Date(cursor.getFullYear(),cursor.getMonth()+1,1):masDias(lunesDe(cursor),7);if(vista==="mes")cursor=limitar(cursor);diaMovil=0;pintar(true)};
  $("#panel").onclick=()=>{const on=document.body.classList.toggle("ver-panel");$("#panel").setAttribute("aria-expanded",on)};
  let girado, ancho=window.innerWidth;   // repintar solo al girar o cambiar el ancho (no al ocultarse la barra del navegador)
  window.addEventListener("resize",()=>{if(window.innerWidth===ancho)return;ancho=window.innerWidth;clearTimeout(girado);girado=setTimeout(()=>pintar(false),150)});
  cursor=limitar(new Date(HOYD)); diaMovil=Math.min((cursor.getDay()+6)%7,N-1);
  pintar(true);
})();
</script>
</body>
</html>
'''


if __name__ == "__main__":
    main()
