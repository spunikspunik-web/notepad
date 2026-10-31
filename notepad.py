#!/usr/bin/env python3
"""Bloc de notas para Linux — réplica del Bloc de notas de Windows 11 (PyQt6).

Pestañas, sesión restaurable, buscar/reemplazar integrado, ir a, zoom,
codificaciones, saltos de línea, impresión con encabezado y pie, tema
claro/oscuro/sistema, configuración, Markdown básico y más.

Uso:  python3 notepad.py [--new] [archivos...]
"""
import itertools
import json
import os
import re
import subprocess
import sys
from urllib.parse import quote

from PyQt6.QtCore import (QDate, QDateTime, QFileSystemWatcher, QMarginsF,
                          QPoint, QRectF, QSettings, QSizeF, QStandardPaths,
                          Qt, QTime, QTimer, QUrl, pyqtSignal)
from PyQt6.QtGui import (QAbstractTextDocumentLayout, QAction, QActionGroup,
                         QColor, QDesktopServices, QFont, QFontDatabase,
                         QFontMetricsF, QGuiApplication, QIcon, QKeySequence,
                         QPageLayout, QPageSize, QPainter, QPalette,
                         QShortcut, QTextCursor, QTextDocument, QTextOption)
from PyQt6.QtPrintSupport import QPrintDialog, QPrinter
from PyQt6.QtWidgets import (QApplication, QCheckBox, QComboBox, QDialog,
                             QDoubleSpinBox, QFileDialog, QFontDialog,
                             QFormLayout, QFrame, QGroupBox, QHBoxLayout,
                             QInputDialog, QLabel, QLineEdit, QMainWindow,
                             QMenu, QMenuBar, QMessageBox, QPlainTextEdit,
                             QPushButton, QRadioButton, QSizePolicy,
                             QStackedWidget, QTabBar, QTextEdit, QToolButton,
                             QVBoxLayout, QWidget)

APP_NAME = "Bloc de notas"
FILTER_OPEN = "Todos los archivos (*);;Documentos de texto (*.txt)"
FILTER_SAVE = "Documentos de texto (*.txt);;Todos los archivos (*)"
BOM8 = b"\xef\xbb\xbf"
ENCODINGS = ["UTF-8", "UTF-8 con BOM", "UTF-16 LE", "UTF-16 BE", "ANSI"]
EOLS = {"Windows (CRLF)": "\r\n", "Macintosh (CR)": "\r", "Unix (LF)": "\n"}
DEFAULT_EOL = "Windows (CRLF)" if os.name == "nt" else "Unix (LF)"
MAX_MATCHES = 5000
SYS_PALETTE = None

UNICODE_CONTROLS = [
    ("LRM", "Marca de izquierda a derecha", "‎"),
    ("RLM", "Marca de derecha a izquierda", "‏"),
    ("ZWJ", "Unión de ancho cero", "‍"),
    ("ZWNJ", "No unión de ancho cero", "‌"),
    ("LRE", "Inicio de incrustación de izquierda a derecha", "‪"),
    ("RLE", "Inicio de incrustación de derecha a izquierda", "‫"),
    ("LRO", "Inicio de anulación de izquierda a derecha", "‭"),
    ("RLO", "Inicio de anulación de derecha a izquierda", "‮"),
    ("PDF", "Fin de formato direccional emergente", "‬"),
    ("NADS", "Formas de dígitos nacionales", "⁮"),
    ("NODS", "Formas de dígitos nominales", "⁯"),
    ("ASS", "Activar conformación simétrica", "⁫"),
    ("ISS", "Inhibir conformación simétrica", "⁪"),
    ("AAFS", "Activar conformación de formas árabes", "⁭"),
    ("IAFS", "Inhibir conformación de formas árabes", "⁬"),
    ("RS", "Separador de registro", "\u001e"),
    ("US", "Separador de unidad", "\u001f"),
]

LIGHT = dict(tabrow="#e9e9e9", rowbg="#f9f9f9", base="#ffffff",
             menu="#fcfcfc", fg="#1b1b1b", muted="#8a8a8a",
             muted_fg="#5d5d5d", border="#e0e0e0", hover="#ececec",
             button="#fdfdfd", accent="#005fb8", accent_fg="#ffffff",
             accent_soft="#d6e7f7", sel="#99c9ef", sel_fg="#000000",
             match="#fff2a8", match_cur="#ffb86b")
DARK = dict(tabrow="#1c1c1c", rowbg="#2b2b2b", base="#202020",
            menu="#2c2c2c", fg="#ffffff", muted="#8b8b8b",
            muted_fg="#c5c5c5", border="#3b3b3b", hover="#383838",
            button="#363636", accent="#60cdff", accent_fg="#000000",
            accent_soft="#1b3a52", sel="#264f78", sel_fg="#ffffff",
            match="#5b4d00", match_cur="#b45f06")


# --------------------------------------------------------------------------
# Utilidades: codificación, saltos de línea, tema, ajustes
# --------------------------------------------------------------------------
def decode_with(data, enc):
    if enc == "UTF-8 con BOM":
        if data.startswith(BOM8):
            data = data[3:]
        return data.decode("utf-8", "replace")
    if enc == "UTF-8":
        return data.decode("utf-8", "replace")
    if enc == "UTF-16 LE":
        if data.startswith(b"\xff\xfe"):
            data = data[2:]
        return data.decode("utf-16-le", "replace")
    if enc == "UTF-16 BE":
        if data.startswith(b"\xfe\xff"):
            data = data[2:]
        return data.decode("utf-16-be", "replace")
    return data.decode("cp1252", "replace")


def detect_and_decode(data):
    if data.startswith(BOM8):
        enc = "UTF-8 con BOM"
    elif data.startswith(b"\xff\xfe"):
        enc = "UTF-16 LE"
    elif data.startswith(b"\xfe\xff"):
        enc = "UTF-16 BE"
    else:
        try:
            data.decode("utf-8")
            enc = "UTF-8"
        except UnicodeDecodeError:
            enc = "ANSI"
    return decode_with(data, enc), enc


def encode_with(text, enc, errors="strict"):
    if enc == "UTF-8 con BOM":
        return BOM8 + text.encode("utf-8", errors)
    if enc == "UTF-16 LE":
        return b"\xff\xfe" + text.encode("utf-16-le", errors)
    if enc == "UTF-16 BE":
        return b"\xfe\xff" + text.encode("utf-16-be", errors)
    if enc == "ANSI":
        return text.encode("cp1252", errors)
    return text.encode("utf-8", errors)


def detect_eol(text):
    crlf = text.count("\r\n")
    lf = text.count("\n") - crlf
    cr = text.count("\r") - crlf
    if crlf == lf == cr == 0:
        return DEFAULT_EOL
    if crlf >= lf and crlf >= cr:
        return "Windows (CRLF)"
    return "Unix (LF)" if lf >= cr else "Macintosh (CR)"


def normalize_nl(text):
    return text.replace("\r\n", "\n").replace("\r", "\n")


def read_list(settings, key):
    v = settings.value(key, [])
    if v is None:
        return []
    if isinstance(v, str):
        return [v] if v else []
    return [str(x) for x in v]


def data_dir():
    base = QStandardPaths.writableLocation(
        QStandardPaths.StandardLocation.GenericDataLocation)
    path = os.path.join(base, "bloc-de-notas")
    os.makedirs(path, exist_ok=True)
    return path


def system_is_dark():
    try:
        scheme = QGuiApplication.styleHints().colorScheme()
        if scheme == Qt.ColorScheme.Dark:
            return True
        if scheme == Qt.ColorScheme.Light:
            return False
    except Exception:
        pass
    pal = SYS_PALETTE or QApplication.palette()
    return pal.color(QPalette.ColorRole.Window).lightness() < 128


def make_palette(c):
    p = QPalette()
    R = QPalette.ColorRole
    for role, key in ((R.Window, "rowbg"), (R.Base, "base"),
                      (R.AlternateBase, "rowbg"), (R.Button, "button"),
                      (R.ToolTipBase, "menu"), (R.Highlight, "sel"),
                      (R.HighlightedText, "sel_fg"), (R.Link, "accent"),
                      (R.PlaceholderText, "muted")):
        p.setColor(role, QColor(c[key]))
    for role in (R.WindowText, R.Text, R.ButtonText, R.ToolTipText):
        p.setColor(role, QColor(c["fg"]))
    for role in (R.WindowText, R.Text, R.ButtonText):
        p.setColor(QPalette.ColorGroup.Disabled, role, QColor(c["muted"]))
    return p


def build_qss(c):
    return f"""
    QMainWindow, QDialog {{ background: {c['rowbg']}; }}
    #tabRow {{ background: {c['tabrow']}; }}
    #menuRow {{ background: {c['rowbg']}; }}
    QMenuBar {{ background: transparent; padding: 3px 2px; }}
    QMenuBar::item {{ padding: 5px 11px; border-radius: 5px;
                      background: transparent; }}
    QMenuBar::item:selected {{ background: {c['hover']}; }}
    QMenu {{ background: {c['menu']}; border: 1px solid {c['border']};
             border-radius: 8px; padding: 5px; }}
    QMenu::item {{ padding: 7px 30px 7px 22px; border-radius: 4px;
                   margin: 1px 2px; }}
    QMenu::item:selected {{ background: {c['hover']}; color: {c['fg']}; }}
    QMenu::item:disabled {{ color: {c['muted']}; }}
    QMenu::separator {{ height: 1px; background: {c['border']};
                        margin: 4px 8px; }}
    QTabBar {{ background: transparent; }}
    QTabBar::tab {{ background: transparent; padding: 7px 12px;
                    margin: 5px 1px 0 1px; min-width: 110px;
                    max-width: 220px; color: {c['muted_fg']};
                    border-top-left-radius: 8px;
                    border-top-right-radius: 8px; }}
    QTabBar::tab:selected {{ background: {c['rowbg']}; color: {c['fg']}; }}
    QTabBar::tab:hover:!selected {{ background: {c['hover']}; }}
    QToolButton {{ border: none; border-radius: 5px; padding: 4px 9px;
                   background: transparent; }}
    QToolButton:hover {{ background: {c['hover']}; }}
    QToolButton:checked {{ background: {c['accent_soft']}; }}
    QStatusBar {{ background: {c['rowbg']};
                  border-top: 1px solid {c['border']}; }}
    QStatusBar QLabel {{ padding: 2px 10px; }}
    QStatusBar::item {{ border: none; }}
    QLabel[clickable="true"]:hover {{ background: {c['hover']};
                                      border-radius: 4px; }}
    #findBar {{ background: {c['rowbg']};
                border-bottom: 1px solid {c['border']}; }}
    QPushButton {{ padding: 5px 14px; border: 1px solid {c['border']};
                   border-radius: 5px; background: {c['button']}; }}
    QPushButton:hover {{ background: {c['hover']}; }}
    QPushButton:default {{ background: {c['accent']};
                           color: {c['accent_fg']}; border: none; }}
    QLineEdit {{ padding: 4px 6px; border: 1px solid {c['border']};
                 border-bottom: 2px solid {c['accent']};
                 border-radius: 4px; background: {c['base']}; }}
    QLineEdit[error="true"] {{ border-bottom: 2px solid #c42b1c; }}
    QComboBox, QDoubleSpinBox {{ padding: 4px 6px;
                 border: 1px solid {c['border']}; border-radius: 4px; }}
    QGroupBox {{ border: 1px solid {c['border']}; border-radius: 8px;
                 margin-top: 12px; padding: 12px 10px 8px 10px; }}
    QGroupBox::title {{ subcontrol-origin: margin; left: 12px;
                        padding: 0 4px; }}
    QScrollBar:vertical {{ background: transparent; width: 14px; margin: 0; }}
    QScrollBar::handle:vertical {{ background: {c['border']};
        border-radius: 3px; min-height: 30px; margin: 2px 4px; }}
    QScrollBar::handle:vertical:hover {{ background: {c['muted']}; }}
    QScrollBar:horizontal {{ background: transparent; height: 14px;
                             margin: 0; }}
    QScrollBar::handle:horizontal {{ background: {c['border']};
        border-radius: 3px; min-width: 30px; margin: 4px 2px; }}
    QScrollBar::handle:horizontal:hover {{ background: {c['muted']}; }}
    QScrollBar::add-line, QScrollBar::sub-line {{ width: 0; height: 0; }}
    QScrollBar::add-page, QScrollBar::sub-page {{ background: transparent; }}
    """


# --------------------------------------------------------------------------
# Editor (una pestaña)
# --------------------------------------------------------------------------
class Editor(QPlainTextEdit):
    zoomRequested = pyqtSignal(int)
    filesDropped = pyqtSignal(list)

    def __init__(self, uid, font, wrap):
        super().__init__()
        self.uid = uid
        self.path = None
        self.eol = DEFAULT_EOL
        self.encoding = "UTF-8"
        self.mtime = None
        self.rtl = False
        self.show_ws = False
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setWordWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
        self.set_wrap(wrap)
        self.document().setDocumentMargin(10)
        self.setFont(font)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)

    def setFont(self, font):
        super().setFont(font)
        self.setTabStopDistance(8 * self.fontMetrics().horizontalAdvance(" "))

    def set_wrap(self, on):
        self.setLineWrapMode(QPlainTextEdit.LineWrapMode.WidgetWidth
                             if on else QPlainTextEdit.LineWrapMode.NoWrap)

    def set_rtl(self, on):
        self.rtl = on
        opt = self.document().defaultTextOption()
        opt.setTextDirection(Qt.LayoutDirection.RightToLeft
                             if on else Qt.LayoutDirection.LeftToRight)
        self.document().setDefaultTextOption(opt)

    def set_show_whitespace(self, on):
        self.show_ws = on
        opt = self.document().defaultTextOption()
        flag = QTextOption.Flag.ShowTabsAndSpaces
        flags = opt.flags()
        if on:
            flags |= flag
        else:
            flags &= ~flag
        opt.setFlags(flags)
        self.document().setDefaultTextOption(opt)

    def name(self):
        return os.path.basename(self.path) if self.path else "Sin título"

    def title(self):
        if self.path:
            return os.path.basename(self.path)
        first = self.document().firstBlock().text().strip()
        if not first:
            return "Sin título"
        return first if len(first) <= 24 else first[:23] + "…"

    def wheelEvent(self, e):
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            dy = e.angleDelta().y()
            if dy:
                self.zoomRequested.emit(10 if dy > 0 else -10)
            e.accept()
            return
        super().wheelEvent(e)

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
        else:
            super().dragEnterEvent(e)

    def dragMoveEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
        else:
            super().dragMoveEvent(e)

    def dropEvent(self, e):
        md = e.mimeData()
        if md.hasUrls():
            paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
            if paths:
                self.filesDropped.emit(paths)
                e.acceptProposedAction()
                return
        super().dropEvent(e)


# --------------------------------------------------------------------------
# Barra de búsqueda / reemplazo integrada
# --------------------------------------------------------------------------
class FindEdit(QLineEdit):
    shiftReturn = pyqtSignal()

    def keyPressEvent(self, e):
        if (e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter)
                and e.modifiers() & Qt.KeyboardModifier.ShiftModifier):
            self.shiftReturn.emit()
            return
        super().keyPressEvent(e)


class FindBar(QFrame):
    def __init__(self, win):
        super().__init__(win)
        self.win = win
        self.setObjectName("findBar")

        self.find_edit = FindEdit()
        self.find_edit.setPlaceholderText("Buscar")
        self.repl_edit = QLineEdit()
        self.repl_edit.setPlaceholderText("Reemplazar")

        def tbtn(text, tip, checkable=False, checked=False):
            b = QToolButton()
            b.setText(text)
            b.setToolTip(tip)
            b.setCheckable(checkable)
            b.setChecked(checked)
            b.setAutoRaise(True)
            return b

        self.btn_toggle = tbtn("▸", "Mostrar u ocultar reemplazar")
        self.btn_case = tbtn("Aa", "Coincidir mayúsculas y minúsculas", True)
        self.btn_word = tbtn("ab", "Coincidir palabra completa", True)
        self.btn_wrap = tbtn("↻", "Volver al principio al llegar al final",
                             True, True)
        self.btn_prev = tbtn("↑", "Buscar anterior (Mayús+F3)")
        self.btn_next = tbtn("↓", "Buscar siguiente (F3)")
        self.btn_close = tbtn("✕", "Cerrar (Esc)")
        self.lbl = QLabel("")
        self.lbl.setMinimumWidth(90)
        self.btn_rep = QPushButton("Reemplazar")
        self.btn_rep_all = QPushButton("Reemplazar todo")

        row1 = QHBoxLayout()
        row1.setContentsMargins(8, 6, 8, 2)
        row1.setSpacing(4)
        for w in (self.btn_toggle,):
            row1.addWidget(w)
        row1.addWidget(self.find_edit, 1)
        for w in (self.btn_case, self.btn_word, self.btn_wrap, self.lbl,
                  self.btn_prev, self.btn_next, self.btn_close):
            row1.addWidget(w)

        self.rep_row = QWidget()
        row2 = QHBoxLayout(self.rep_row)
        row2.setContentsMargins(8, 2, 8, 6)
        row2.setSpacing(4)
        spacer = QWidget()
        spacer.setFixedWidth(self.btn_toggle.sizeHint().width())
        row2.addWidget(spacer)
        row2.addWidget(self.repl_edit, 1)
        row2.addWidget(self.btn_rep)
        row2.addWidget(self.btn_rep_all)
        self.rep_row.hide()

        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        lay.addLayout(row1)
        lay.addWidget(self.rep_row)

        self.find_edit.textChanged.connect(lambda _t: self.find(typing=True))
        self.find_edit.returnPressed.connect(lambda: self.find())
        self.find_edit.shiftReturn.connect(lambda: self.find(backward=True))
        self.btn_next.clicked.connect(lambda: self.find())
        self.btn_prev.clicked.connect(lambda: self.find(backward=True))
        self.btn_close.clicked.connect(self.close_bar)
        self.btn_toggle.clicked.connect(self._toggle_replace)
        self.btn_case.toggled.connect(lambda _c: self.refresh())
        self.btn_word.toggled.connect(lambda _c: self.refresh())
        self.btn_rep.clicked.connect(self.replace_one)
        self.btn_rep_all.clicked.connect(self.replace_all)

    # -- apertura / cierre --
    def _toggle_replace(self):
        self.set_replace_visible(not self.rep_row.isVisible())

    def set_replace_visible(self, on):
        self.rep_row.setVisible(on)
        self.btn_toggle.setText("▾" if on else "▸")

    def open(self, replace=False):
        ed = self.win.editor()
        sel = ed.textCursor().selectedText() if ed else ""
        self.show()
        if replace:
            self.set_replace_visible(True)
        if sel and " " not in sel:
            self.find_edit.setText(sel)
        else:
            self.refresh()
        self.find_edit.setFocus()
        self.find_edit.selectAll()

    def close_bar(self):
        if not self.isVisible():
            return
        self.hide()
        self.win.clear_highlights()
        ed = self.win.editor()
        if ed:
            ed.setFocus()

    # -- búsqueda --
    def _flags(self, backward=False):
        f = QTextDocument.FindFlag(0)
        if self.btn_case.isChecked():
            f |= QTextDocument.FindFlag.FindCaseSensitively
        if self.btn_word.isChecked():
            f |= QTextDocument.FindFlag.FindWholeWords
        if backward:
            f |= QTextDocument.FindFlag.FindBackward
        return f

    def _mark_error(self, on):
        self.find_edit.setProperty("error", on)
        st = self.find_edit.style()
        st.unpolish(self.find_edit)
        st.polish(self.find_edit)

    def find(self, backward=False, typing=False):
        ed = self.win.editor()
        text = self.find_edit.text()
        if ed is None:
            return False
        if not text:
            self._mark_error(False)
            self.lbl.setText("")
            self.win.clear_highlights()
            return False
        doc = ed.document()
        cur = ed.textCursor()
        if typing:
            cur.setPosition(cur.selectionStart())
        found = doc.find(text, cur, self._flags(backward))
        if found.isNull() and self.btn_wrap.isChecked():
            c = QTextCursor(doc)
            c.movePosition(QTextCursor.MoveOperation.End if backward
                           else QTextCursor.MoveOperation.Start)
            found = doc.find(text, c, self._flags(backward))
        if found.isNull():
            self._mark_error(True)
            self.refresh()
            return False
        self._mark_error(False)
        ed.setTextCursor(found)
        ed.ensureCursorVisible()
        self.refresh()
        return True

    def refresh(self):
        """Resalta coincidencias y actualiza el contador «x de y»."""
        ed = self.win.editor()
        if ed is None:
            return
        text = self.find_edit.text()
        sels = []
        total = current = 0
        if text and self.isVisible():
            c = self.win.colors
            doc = ed.document()
            sel = ed.textCursor()
            flags = self._flags()
            cur = QTextCursor(doc)
            while total < MAX_MATCHES:
                cur = doc.find(text, cur, flags)
                if cur.isNull():
                    break
                total += 1
                is_cur = (sel.hasSelection()
                          and cur.selectionStart() == sel.selectionStart()
                          and cur.selectionEnd() == sel.selectionEnd())
                if is_cur:
                    current = total
                es = QTextEdit.ExtraSelection()
                es.cursor = QTextCursor(cur)
                es.format.setBackground(
                    QColor(c["match_cur"] if is_cur else c["match"]))
                sels.append(es)
        ed.setExtraSelections(sels)
        if not text or not self.isVisible():
            self.lbl.setText("")
        elif total == 0:
            self.lbl.setText("Sin resultados")
        else:
            shown = f"{total}+" if total >= MAX_MATCHES else str(total)
            self.lbl.setText(f"{current} de {shown}" if current
                             else f"{shown} resultados")

    # -- reemplazo --
    def replace_one(self):
        ed = self.win.editor()
        text = self.find_edit.text()
        if ed is None or not text:
            return
        cur = ed.textCursor()
        sel = cur.selectedText()
        same = (sel == text if self.btn_case.isChecked()
                else sel.casefold() == text.casefold())
        if cur.hasSelection() and same:
            cur.insertText(self.repl_edit.text())
            ed.setTextCursor(cur)
        self.find()

    def replace_all(self):
        ed = self.win.editor()
        text = self.find_edit.text()
        if ed is None or not text:
            return
        flags = self._flags()
        doc = ed.document()
        cur = QTextCursor(doc)
        cur.beginEditBlock()
        count = 0
        while True:
            found = doc.find(text, cur, flags)
            if found.isNull():
                break
            found.insertText(self.repl_edit.text())
            cur = found
            count += 1
        cur.endEditBlock()
        self.refresh()
        self.lbl.setText(f"{count} reemplazos")


# --------------------------------------------------------------------------
# Etiqueta clicable (barra de estado)
# --------------------------------------------------------------------------
class ClickLabel(QLabel):
    clicked = pyqtSignal()

    def __init__(self, text=""):
        super().__init__(text)
        self.setProperty("clickable", True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
        super().mouseReleaseEvent(e)


# --------------------------------------------------------------------------
# Configurar página (papel, orientación, márgenes, encabezado y pie)
# --------------------------------------------------------------------------
PAPERS = [("A4", QPageSize.PageSizeId.A4),
          ("Carta (Letter)", QPageSize.PageSizeId.Letter),
          ("Legal", QPageSize.PageSizeId.Legal),
          ("A3", QPageSize.PageSizeId.A3),
          ("A5", QPageSize.PageSizeId.A5),
          ("Ejecutivo", QPageSize.PageSizeId.Executive)]


def default_page_layout():
    return QPageLayout(QPageSize(QPageSize.PageSizeId.A4),
                       QPageLayout.Orientation.Portrait,
                       QMarginsF(20, 20, 20, 20),
                       QPageLayout.Unit.Millimeter)


class PageSetupDialog(QDialog):
    def __init__(self, parent, layout, header, footer):
        super().__init__(parent)
        self.setWindowTitle("Configurar página")
        self.setMinimumWidth(420)

        self.paper = QComboBox()
        for name, pid in PAPERS:
            self.paper.addItem(name)
        for i, (_n, pid) in enumerate(PAPERS):
            if layout.pageSize().id() == pid:
                self.paper.setCurrentIndex(i)

        self.rb_port = QRadioButton("Vertical")
        self.rb_land = QRadioButton("Horizontal")
        (self.rb_land if layout.orientation()
         == QPageLayout.Orientation.Landscape else self.rb_port
         ).setChecked(True)
        orient = QHBoxLayout()
        orient.addWidget(self.rb_port)
        orient.addWidget(self.rb_land)

        m = layout.margins(QPageLayout.Unit.Millimeter)
        self.spins = {}
        marg = QFormLayout()
        for key, label, val in (("l", "Izquierdo", m.left()),
                                ("t", "Superior", m.top()),
                                ("r", "Derecho", m.right()),
                                ("b", "Inferior", m.bottom())):
            sp = QDoubleSpinBox()
            sp.setRange(0, 60)
            sp.setSuffix(" mm")
            sp.setValue(val)
            self.spins[key] = sp
            marg.addRow(label + ":", sp)

        self.header = QLineEdit(header)
        self.footer = QLineEdit(footer)
        hf = QFormLayout()
        hf.addRow("Encabezado:", self.header)
        hf.addRow("Pie de página:", self.footer)
        hint = QLabel("Códigos: &f nombre del archivo, &p página, &d fecha, "
                      "&t hora, &l &c &r alineación, && un &")
        hint.setWordWrap(True)

        ok = QPushButton("Aceptar")
        ok.setDefault(True)
        ok.clicked.connect(self.accept)
        cancel = QPushButton("Cancelar")
        cancel.clicked.connect(self.reject)
        btns = QHBoxLayout()
        btns.addStretch(1)
        btns.addWidget(ok)
        btns.addWidget(cancel)

        g1 = QGroupBox("Papel")
        f1 = QFormLayout(g1)
        f1.addRow("Tamaño:", self.paper)
        f1.addRow("Orientación:", orient)
        g2 = QGroupBox("Márgenes")
        g2.setLayout(marg)
        g3 = QGroupBox("Encabezado y pie")
        v3 = QVBoxLayout(g3)
        v3.addLayout(hf)
        v3.addWidget(hint)

        lay = QVBoxLayout(self)
        lay.addWidget(g1)
        lay.addWidget(g2)
        lay.addWidget(g3)
        lay.addLayout(btns)

    def result_layout(self):
        pid = PAPERS[self.paper.currentIndex()][1]
        orient = (QPageLayout.Orientation.Landscape if self.rb_land.isChecked()
                  else QPageLayout.Orientation.Portrait)
        s = self.spins
        margins = QMarginsF(s["l"].value(), s["t"].value(),
                            s["r"].value(), s["b"].value())
        return QPageLayout(QPageSize(pid), orient, margins,
                           QPageLayout.Unit.Millimeter)


# --------------------------------------------------------------------------
# Configuración (tema, fuente, ajuste de línea, apertura, inicio)
# --------------------------------------------------------------------------
class SettingsDialog(QDialog):
    def __init__(self, win):
        super().__init__(win)
        self.win = win
        self.setWindowTitle("Configuración")
        self.setMinimumWidth(520)

        self.theme = QComboBox()
        self.theme.addItem("Claro", "light")
        self.theme.addItem("Oscuro", "dark")
        self.theme.addItem("Usar configuración del sistema", "system")
        self.theme.setCurrentIndex(
            max(0, self.theme.findData(win.theme_mode)))
        self.theme.currentIndexChanged.connect(
            lambda _i: win.set_theme_mode(self.theme.currentData()))

        self.lbl_font = QLabel()
        btn_font = QPushButton("Cambiar fuente...")
        btn_font.clicked.connect(self._pick_font)
        self._refresh_font()
        frow = QHBoxLayout()
        frow.addWidget(self.lbl_font, 1)
        frow.addWidget(btn_font)

        self.wrap = QCheckBox("Ajuste de línea")
        self.wrap.setChecked(win.wrap)
        self.wrap.toggled.connect(win.act_wrap.setChecked)

        self.open_mode = QComboBox()
        self.open_mode.addItem("Abrir en una pestaña nueva", False)
        self.open_mode.addItem("Abrir en una ventana nueva", True)
        self.open_mode.setCurrentIndex(1 if win.open_new_window else 0)
        self.open_mode.currentIndexChanged.connect(
            lambda _i: win.set_open_new_window(self.open_mode.currentData()))

        self.startup = QComboBox()
        self.startup.addItem("Abrir el contenido de la sesión anterior y "
                             "los cambios sin guardar", True)
        self.startup.addItem("Iniciar una nueva sesión y descartar los "
                             "cambios sin guardar", False)
        self.startup.setCurrentIndex(0 if win.restore_session else 1)
        self.startup.currentIndexChanged.connect(
            lambda _i: win.set_restore_session(self.startup.currentData()))

        g1 = QGroupBox("Aspecto")
        f1 = QFormLayout(g1)
        f1.addRow("Tema de la aplicación:", self.theme)
        g2 = QGroupBox("Formato de texto")
        v2 = QVBoxLayout(g2)
        v2.addLayout(frow)
        v2.addWidget(self.wrap)
        g3 = QGroupBox("Abrir archivos")
        v3 = QVBoxLayout(g3)
        v3.addWidget(self.open_mode)
        g4 = QGroupBox("Al iniciar el Bloc de notas")
        v4 = QVBoxLayout(g4)
        v4.addWidget(self.startup)

        close = QPushButton("Cerrar")
        close.setDefault(True)
        close.clicked.connect(self.accept)
        lay = QVBoxLayout(self)
        for g in (g1, g2, g3, g4):
            lay.addWidget(g)
        row = QHBoxLayout()
        row.addStretch(1)
        row.addWidget(close)
        lay.addLayout(row)

    def _refresh_font(self):
        f = self.win.font_
        style = f.styleName()
        self.lbl_font.setText(
            f"{f.family()}, {style + ', ' if style else ''}{f.pointSize()} pt")

    def _pick_font(self):
        self.win.choose_font()
        self._refresh_font()


# --------------------------------------------------------------------------
# Ventana principal
# --------------------------------------------------------------------------
class Notepad(QMainWindow):
    def __init__(self, files=(), new_session=False):
        super().__init__()
        self.owner = not new_session
        s = self.settings = QSettings("BlocDeNotas", "Notepad")
        mono = QFontDatabase.systemFont(QFontDatabase.SystemFont.FixedFont)
        self.font_ = QFont()
        fs = s.value("font", "", type=str)
        if not (fs and self.font_.fromString(fs)):
            self.font_ = QFont(mono.family(), 11)
        self.zoom = s.value("zoom", 100, type=int)
        self.wrap = s.value("wrap", True, type=bool)
        self.theme_mode = s.value("theme", "system", type=str)
        self.show_status = s.value("status_bar", True, type=bool)
        self.open_new_window = s.value("open_new_window", False, type=bool)
        self.restore_session = s.value("restore_session", True, type=bool)
        self.header = s.value("print_header", "&f", type=str)
        self.footer = s.value("print_footer", "Página &p", type=str)
        self.page_layout = self._load_page_layout()
        self.dark = False
        self.colors = LIGHT
        self.docs = {}
        self._uid = itertools.count(1)
        self._empty_session = False
        self._reloading = False

        self.watcher = QFileSystemWatcher(self)
        self.watcher.fileChanged.connect(self._file_changed)
        self._find_timer = QTimer(self, singleShot=True, interval=150)
        self._find_timer.timeout.connect(self._refresh_find)
        self._session_timer = QTimer(self, interval=30000)
        self._session_timer.timeout.connect(self._autosave_session)

        self.setWindowIcon(QIcon.fromTheme("accessories-text-editor"))
        self.setAcceptDrops(True)
        self._build_ui()
        self._build_menus()
        self._build_status()
        QShortcut(QKeySequence("Esc"), self, activated=self.findbar.close_bar)
        geo = s.value("geometry")
        if geo is not None:
            self.restoreGeometry(geo)
        else:
            self.resize(1000, 650)

        self.apply_theme()
        try:
            QGuiApplication.styleHints().colorSchemeChanged.connect(
                lambda _s: self.theme_mode == "system" and self.apply_theme())
        except Exception:
            pass

        if self.owner and self.restore_session:
            self.load_session()
        for f in files:
            self.open_path(f)
        if self.tabbar.count() == 0:
            self.new_tab()
        if self.owner:
            self._session_timer.start()
        self.statusBar().setVisible(self.show_status)

    # ---------------- interfaz ----------------
    def _build_ui(self):
        central = QWidget()
        outer = QVBoxLayout(central)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        tab_row = QWidget()
        tab_row.setObjectName("tabRow")
        tab_row.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        th = QHBoxLayout(tab_row)
        th.setContentsMargins(8, 0, 8, 0)
        th.setSpacing(2)
        self.tabbar = QTabBar()
        self.tabbar.setTabsClosable(True)
        self.tabbar.setMovable(True)
        self.tabbar.setExpanding(False)
        self.tabbar.setDrawBase(False)
        self.tabbar.setUsesScrollButtons(True)
        self.tabbar.setElideMode(Qt.TextElideMode.ElideRight)
        self.tabbar.setContextMenuPolicy(
            Qt.ContextMenuPolicy.CustomContextMenu)
        self.tabbar.tabCloseRequested.connect(self.close_tab)
        self.tabbar.currentChanged.connect(self._on_current_changed)
        self.tabbar.customContextMenuRequested.connect(self.tab_menu)
        self.btn_plus = QToolButton()
        self.btn_plus.setText("+")
        self.btn_plus.setToolTip("Nueva pestaña (Ctrl+N)")
        self.btn_plus.clicked.connect(lambda: self.new_tab())
        th.addWidget(self.tabbar)
        th.addWidget(self.btn_plus)
        th.addStretch(1)
        outer.addWidget(tab_row)

        menu_row = QWidget()
        menu_row.setObjectName("menuRow")
        menu_row.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        mh = QHBoxLayout(menu_row)
        mh.setContentsMargins(6, 0, 10, 0)
        self.menubar = QMenuBar()
        self.menubar.setNativeMenuBar(False)
        self.menubar.setSizePolicy(QSizePolicy.Policy.Maximum,
                                   QSizePolicy.Policy.Preferred)
        self.btn_gear = QToolButton()
        self.btn_gear.setText("⚙")
        self.btn_gear.setToolTip("Configuración")
        self.btn_gear.clicked.connect(self.show_settings)
        mh.addWidget(self.menubar)
        mh.addStretch(1)
        mh.addWidget(self.btn_gear)
        outer.addWidget(menu_row)

        self.findbar = FindBar(self)
        self.findbar.hide()
        outer.addWidget(self.findbar)
        self.stack = QStackedWidget()
        outer.addWidget(self.stack, 1)
        self.setCentralWidget(central)

    def _act(self, menu, text, slot, shortcut=None, checkable=False,
             checked=False):
        a = QAction(text, self)
        if shortcut:
            seqs = shortcut if isinstance(shortcut, (list, tuple)) \
                else [shortcut]
            a.setShortcuts([QKeySequence(x) for x in seqs])
        if checkable:
            a.setCheckable(True)
            a.setChecked(checked)
            a.toggled.connect(slot)
        else:
            a.triggered.connect(lambda _=False: slot())
        menu.addAction(a)
        self.addAction(a)
        return a

    def _build_menus(self):
        mb = self.menubar
        A = self._act

        m = mb.addMenu("Archivo")
        A(m, "Nueva pestaña", self.new_tab, "Ctrl+N")
        A(m, "Nueva ventana", self.spawn_window, "Ctrl+Shift+N")
        A(m, "Abrir...", self.open_dialog, "Ctrl+O")
        self.menu_recent = m.addMenu("Abrir reciente")
        self.menu_recent.aboutToShow.connect(self._fill_recent)
        m.addSeparator()
        A(m, "Guardar", self.save, "Ctrl+S")
        A(m, "Guardar como...", self.save_as, "Ctrl+Shift+S")
        A(m, "Guardar todo", self.save_all, "Ctrl+Alt+S")
        m.addSeparator()
        A(m, "Configurar página...", self.page_setup)
        A(m, "Imprimir...", self.print_dialog, "Ctrl+P")
        m.addSeparator()
        A(m, "Cerrar pestaña", lambda: self.close_tab(
            self.tabbar.currentIndex()), "Ctrl+W")
        A(m, "Cerrar ventana", self.close, "Ctrl+Shift+W")
        A(m, "Salir", QApplication.closeAllWindows)

        m = mb.addMenu("Edición")
        self.menu_edit = m
        self.a_undo = A(m, "Deshacer", lambda: self._ed("undo"), "Ctrl+Z")
        self.a_redo = A(m, "Rehacer", lambda: self._ed("redo"), "Ctrl+Y")
        m.addSeparator()
        self.a_cut = A(m, "Cortar", lambda: self._ed("cut"), "Ctrl+X")
        self.a_copy = A(m, "Copiar", lambda: self._ed("copy"), "Ctrl+C")
        self.a_paste = A(m, "Pegar", lambda: self._ed("paste"), "Ctrl+V")
        self.a_delete = A(m, "Eliminar", self.delete_sel, "Del")
        m.addSeparator()
        self.a_bing = A(m, "Buscar con Bing", self.search_web, "Ctrl+E")
        A(m, "Buscar", lambda: self.findbar.open(False), "Ctrl+F")
        A(m, "Buscar siguiente", lambda: self.find_step(False), "F3")
        A(m, "Buscar anterior", lambda: self.find_step(True), "Shift+F3")
        A(m, "Reemplazar", lambda: self.findbar.open(True), "Ctrl+H")
        self.a_goto = A(m, "Ir a...", self.goto_line, "Ctrl+G")
        m.addSeparator()
        A(m, "Seleccionar todo", lambda: self._ed("selectAll"), "Ctrl+A")
        A(m, "Hora y fecha", self.insert_datetime, "F5")
        self._edit_actions = [self.a_undo, self.a_redo, self.a_cut,
                              self.a_copy, self.a_paste, self.a_delete,
                              self.a_bing, self.a_goto]
        m.aboutToShow.connect(self._edit_menu_show)
        m.aboutToHide.connect(self._edit_menu_hide)

        m = mb.addMenu("Formato")
        self.act_wrap = A(m, "Ajuste de línea", self.set_wrap,
                          checkable=True, checked=self.wrap)
        A(m, "Fuente...", self.choose_font)
        m.addSeparator()
        A(m, "Negrita", lambda: self.md_wrap("**", None, "negrita"),
          "Ctrl+B")
        A(m, "Cursiva", lambda: self.md_wrap("*", None, "cursiva"), "Ctrl+I")
        A(m, "Tachado", lambda: self.md_wrap("~~", None, "tachado"))
        A(m, "Código", lambda: self.md_wrap("`", None, "código"))
        A(m, "Hipervínculo...", self.md_link, "Ctrl+K")
        m.addSeparator()
        A(m, "Lista con viñetas", lambda: self.md_prefix(lambda i: "- "))
        A(m, "Lista numerada",
          lambda: self.md_prefix(lambda i: f"{i + 1}. "))
        hm = m.addMenu("Encabezado")
        for n in range(1, 7):
            A(hm, f"Encabezado {n}", lambda n=n: self.md_heading(n))
        A(hm, "Texto normal", lambda: self.md_heading(0))
        A(m, "Borrar formato", self.md_clear)

        m = mb.addMenu("Ver")
        z = m.addMenu("Zoom")
        A(z, "Acercar", lambda: self.change_zoom(10),
          ["Ctrl+=", "Ctrl++"])
        A(z, "Alejar", lambda: self.change_zoom(-10), "Ctrl+-")
        A(z, "Restaurar zoom predeterminado",
          lambda: self.change_zoom(reset=True), "Ctrl+0")
        self.act_status = A(m, "Barra de estado", self.set_status_visible,
                            checkable=True, checked=self.show_status)
        m.addAction(self.act_wrap)
        m.addSeparator()
        A(m, "Pestaña siguiente", lambda: self.step_tab(1),
          ["Ctrl+Tab", "Ctrl+PgDown"])
        A(m, "Pestaña anterior", lambda: self.step_tab(-1),
          ["Ctrl+Shift+Tab", "Ctrl+PgUp"])

    def _build_status(self):
        sb = self.statusBar()
        sb.setSizeGripEnabled(False)
        self.lbl_pos = QLabel("Ln 1, Col 1")
        self.lbl_pos.setMinimumWidth(110)
        sb.addWidget(self.lbl_pos)
        self.lbl_chars = QLabel("0 caracteres")
        self.lbl_zoom = QLabel("100%")
        self.lbl_eol = ClickLabel("Unix (LF)")
        self.lbl_enc = ClickLabel("UTF-8")
        self.lbl_eol.clicked.connect(self.eol_menu)
        self.lbl_enc.clicked.connect(self.enc_menu)
        for w, width in ((self.lbl_chars, 120), (self.lbl_zoom, 56),
                         (self.lbl_eol, 120), (self.lbl_enc, 100)):
            w.setMinimumWidth(width)
            sb.addPermanentWidget(w)

    # ---------------- tema ----------------
    def apply_theme(self):
        mode = self.theme_mode
        self.dark = mode == "dark" or (mode == "system" and system_is_dark())
        c = self.colors = DARK if self.dark else LIGHT
        app = QApplication.instance()
        app.setStyle("Fusion")
        app.setPalette(make_palette(c))
        self.setStyleSheet(build_qss(c))
        self.findbar.refresh()

    def set_theme_mode(self, mode):
        self.theme_mode = mode
        self.settings.setValue("theme", mode)
        self.apply_theme()

    def show_settings(self):
        SettingsDialog(self).exec()

    def set_open_new_window(self, on):
        self.open_new_window = bool(on)
        self.settings.setValue("open_new_window", self.open_new_window)

    def set_restore_session(self, on):
        self.restore_session = bool(on)
        self.settings.setValue("restore_session", self.restore_session)

    def set_status_visible(self, on):
        self.show_status = on
        self.settings.setValue("status_bar", on)
        self.statusBar().setVisible(on)

    # ---------------- pestañas ----------------
    def editor_at(self, i):
        uid = self.tabbar.tabData(i) if 0 <= i < self.tabbar.count() else None
        return self.docs.get(uid)

    def editor(self):
        return self.editor_at(self.tabbar.currentIndex())

    def index_of(self, ed):
        for i in range(self.tabbar.count()):
            if self.tabbar.tabData(i) == ed.uid:
                return i
        return -1

    def _ed(self, method):
        ed = self.editor()
        if ed:
            getattr(ed, method)()

    def new_tab(self, text="", path=None):
        ed = Editor(next(self._uid), self._zoomed_font(), self.wrap)
        if text:
            ed.setPlainText(text)
        ed.path = path
        ed.document().setModified(False)
        ed.document().modificationChanged.connect(
            lambda _m, e=ed: self._update_title(e))
        ed.cursorPositionChanged.connect(self.update_status)
        ed.textChanged.connect(lambda e=ed: self._text_changed(e))
        ed.zoomRequested.connect(lambda d: self.change_zoom(d))
        ed.filesDropped.connect(self.open_paths)
        ed.customContextMenuRequested.connect(
            lambda pos, e=ed: self.editor_menu(e, e.mapToGlobal(pos)))
        self.docs[ed.uid] = ed
        self.stack.addWidget(ed)
        self.tabbar.blockSignals(True)
        idx = self.tabbar.addTab(ed.title())
        self.tabbar.setTabData(idx, ed.uid)
        self.tabbar.blockSignals(False)
        self.tabbar.setCurrentIndex(idx)
        self._on_current_changed(idx)
        self._update_title(ed)
        return ed

    def _on_current_changed(self, i):
        ed = self.editor_at(i)
        if ed is None:
            return
        self.clear_highlights(except_ed=ed)
        self.stack.setCurrentWidget(ed)
        ed.setFocus()
        self._update_window_title()
        self.update_status()
        if self.findbar.isVisible():
            self.findbar.refresh()

    def activate(self, ed):
        i = self.index_of(ed)
        if i >= 0:
            self.tabbar.setCurrentIndex(i)

    def step_tab(self, d):
        n = self.tabbar.count()
        if n > 1:
            self.tabbar.setCurrentIndex((self.tabbar.currentIndex() + d) % n)

    def _text_changed(self, ed):
        if ed.path is None:
            self._update_title(ed)
        if ed is self.editor():
            self.update_status()
            if self.findbar.isVisible():
                self._find_timer.start()

    def _refresh_find(self):
        if self.findbar.isVisible():
            self.findbar.refresh()

    def clear_highlights(self, except_ed=None):
        for ed in self.docs.values():
            if ed is not except_ed:
                ed.setExtraSelections([])

    def _update_title(self, ed):
        i = self.index_of(ed)
        if i < 0:
            return
        mark = "● " if ed.document().isModified() else ""
        self.tabbar.setTabText(i, mark + ed.title())
        self.tabbar.setTabToolTip(i, ed.path or ed.name())
        if ed is self.editor():
            self._update_window_title()

    def _update_window_title(self):
        ed = self.editor()
        if ed:
            star = "*" if ed.document().isModified() else ""
            self.setWindowTitle(f"{star}{ed.name()} - {APP_NAME}")
        else:
            self.setWindowTitle(APP_NAME)

    def _remove_tab(self, i):
        ed = self.editor_at(i)
        if ed is None:
            return
        self._unwatch(ed.path)
        self.tabbar.removeTab(i)
        self.docs.pop(ed.uid, None)
        self.stack.removeWidget(ed)
        ed.deleteLater()

    def close_tab(self, i):
        ed = self.editor_at(i)
        if ed is None or not self.maybe_save(ed):
            return
        if self.tabbar.count() == 1:
            self._empty_session = True
            ed.document().setModified(False)
            self.close()
            return
        self._remove_tab(i)

    def close_many(self, editors):
        for ed in editors:
            if not self.maybe_save(ed):
                return
            if self.tabbar.count() == 1:
                self._empty_session = True
                ed.document().setModified(False)
                self.close()
                return
            self._remove_tab(self.index_of(ed))

    def tab_menu(self, pos):
        i = self.tabbar.tabAt(pos)
        ed = self.editor_at(i)
        if ed is None:
            return
        allv = [self.editor_at(k) for k in range(self.tabbar.count())]
        m = QMenu(self)
        m.addAction("Cerrar pestaña").triggered.connect(
            lambda: self.close_tab(self.index_of(ed)))
        m.addAction("Cerrar otras pestañas").triggered.connect(
            lambda: self.close_many([e for e in allv if e is not ed]))
        m.addAction("Cerrar pestañas a la derecha").triggered.connect(
            lambda: self.close_many(allv[i + 1:]))
        m.addAction("Cerrar todas las pestañas").triggered.connect(
            lambda: self.close_many(allv))
        m.addSeparator()
        a = m.addAction("Copiar ruta de acceso")
        a.setEnabled(bool(ed.path))
        a.triggered.connect(
            lambda: QApplication.clipboard().setText(ed.path))
        b = m.addAction("Abrir ubicación del archivo")
        b.setEnabled(bool(ed.path))
        b.triggered.connect(lambda: QDesktopServices.openUrl(
            QUrl.fromLocalFile(os.path.dirname(ed.path))))
        m.exec(self.tabbar.mapToGlobal(pos))

    # ---------------- archivos ----------------
    def maybe_save(self, ed):
        if not ed.document().isModified():
            return True
        self.activate(ed)
        box = QMessageBox(self)
        box.setWindowTitle(APP_NAME)
        box.setText(f"¿Quieres guardar los cambios en {ed.name()}?")
        save = box.addButton("Guardar", QMessageBox.ButtonRole.AcceptRole)
        box.addButton("No guardar", QMessageBox.ButtonRole.DestructiveRole)
        cancel = box.addButton("Cancelar", QMessageBox.ButtonRole.RejectRole)
        box.exec()
        clicked = box.clickedButton()
        if clicked is cancel:
            return False
        if clicked is save:
            return self.save_editor(ed)
        return True

    def spawn_window(self, files=()):
        files = [f for f in files if isinstance(f, str)]
        cmd = [sys.executable] if getattr(sys, "frozen", False) \
            else [sys.executable, os.path.abspath(__file__)]
        subprocess.Popen(cmd + ["--new"] + files)

    def _last_dir(self):
        d = self.settings.value("last_dir", "", type=str)
        return d if d and os.path.isdir(d) else os.path.expanduser("~")

    def open_dialog(self):
        paths, _ = QFileDialog.getOpenFileNames(
            self, "Abrir", self._last_dir(), FILTER_OPEN)
        if paths:
            self.settings.setValue("last_dir", os.path.dirname(paths[0]))
            self.open_paths(paths)

    def open_paths(self, paths):
        for p in paths:
            if self.open_new_window:
                self.spawn_window([p])
            else:
                self.open_path(p)

    def add_recent(self, path):
        lst = [p for p in read_list(self.settings, "recent") if p != path]
        self.settings.setValue("recent", ([path] + lst)[:10])

    def _fill_recent(self):
        m = self.menu_recent
        m.clear()
        lst = [p for p in read_list(self.settings, "recent")
               if os.path.exists(p)]
        if not lst:
            m.addAction("(vacío)").setEnabled(False)
            return
        for p in lst:
            m.addAction(p).triggered.connect(
                lambda _=False, p=p: self.open_paths([p]))
        m.addSeparator()
        m.addAction("Borrar elementos recientes").triggered.connect(
            lambda: self.settings.setValue("recent", []))

    def open_path(self, path):
        path = os.path.abspath(path)
        for ed in self.docs.values():
            if ed.path and os.path.abspath(ed.path) == path:
                self.activate(ed)
                return ed
        if not os.path.exists(path):
            r = QMessageBox.question(
                self, APP_NAME,
                f"No se encuentra el archivo:\n{path}\n\n¿Quieres crear uno nuevo?")
            if r != QMessageBox.StandardButton.Yes:
                return None
            try:
                open(path, "wb").close()
            except OSError as e:
                QMessageBox.warning(self, APP_NAME, f"No se pudo crear:\n{e}")
                return None
        try:
            with open(path, "rb") as f:
                data = f.read()
            mtime = os.path.getmtime(path)
        except OSError as e:
            QMessageBox.warning(self, APP_NAME, f"No se pudo abrir:\n{e}")
            return None
        text, enc = detect_and_decode(data)
        eol = detect_eol(text)
        text = normalize_nl(text)
        cur = self.editor()
        if (cur and not cur.path and not cur.document().isModified()
                and cur.document().isEmpty()):
            ed = cur
            ed.setPlainText(text)
        else:
            ed = self.new_tab(text)
        ed.path, ed.eol, ed.encoding, ed.mtime = path, eol, enc, mtime
        ed.document().setModified(False)
        self._watch(path)
        self.add_recent(path)
        self._update_title(ed)
        self.update_status()
        return ed

    def reload_editor(self, ed, enc=None):
        try:
            with open(ed.path, "rb") as f:
                data = f.read()
            ed.mtime = os.path.getmtime(ed.path)
        except OSError as e:
            QMessageBox.warning(self, APP_NAME, f"No se pudo abrir:\n{e}")
            return
        if enc is None:
            text, enc = detect_and_decode(data)
        else:
            text = decode_with(data, enc)
        ed.eol = detect_eol(text)
        text = normalize_nl(text)
        pos = ed.textCursor().position()
        ed.setPlainText(text)
        ed.encoding = enc
        ed.document().setModified(False)
        cur = ed.textCursor()
        cur.setPosition(min(pos, len(text)))
        ed.setTextCursor(cur)
        self._update_title(ed)
        self.update_status()

    # -- vigilancia de cambios externos --
    def _watch(self, path):
        if path and os.path.exists(path) and path not in self.watcher.files():
            self.watcher.addPath(path)

    def _unwatch(self, path):
        if path and path in self.watcher.files():
            self.watcher.removePath(path)

    def _file_changed(self, path):
        for ed in list(self.docs.values()):
            if ed.path and os.path.abspath(ed.path) == os.path.abspath(path):
                QTimer.singleShot(
                    250, lambda e=ed: self._reload_if_changed(e))

    def _reload_if_changed(self, ed):
        path = ed.path
        if not path or ed.uid not in self.docs or not os.path.exists(path):
            return
        self._watch(path)
        try:
            mt = os.path.getmtime(path)
        except OSError:
            return
        if ed.mtime is not None and abs(mt - ed.mtime) < 0.001:
            return
        if self._reloading:
            return
        if ed.document().isModified():
            self._reloading = True
            r = QMessageBox.question(
                self, APP_NAME,
                f"«{ed.name()}» cambió en el disco.\n¿Quieres cargar los "
                "cambios? Se perderán tus modificaciones.")
            self._reloading = False
            if r != QMessageBox.StandardButton.Yes:
                ed.mtime = mt
                return
        self.reload_editor(ed)

    # -- guardar --
    def save(self):
        ed = self.editor()
        return self.save_editor(ed) if ed else False

    def save_as(self):
        ed = self.editor()
        return self.save_editor(ed, True) if ed else False

    def save_all(self):
        for i in range(self.tabbar.count()):
            ed = self.editor_at(i)
            if ed.document().isModified():
                self.activate(ed)
                if not self.save_editor(ed):
                    return

    def _encode_for_save(self, ed, text):
        try:
            return encode_with(text, ed.encoding)
        except UnicodeEncodeError:
            box = QMessageBox(self)
            box.setWindowTitle(APP_NAME)
            box.setText("Este archivo contiene caracteres Unicode que se "
                        f"perderán si lo guardas con la codificación "
                        f"{ed.encoding}.")
            utf8 = box.addButton("Guardar como UTF-8",
                                 QMessageBox.ButtonRole.AcceptRole)
            keep = box.addButton("Guardar de todos modos",
                                 QMessageBox.ButtonRole.DestructiveRole)
            cancel = box.addButton("Cancelar",
                                   QMessageBox.ButtonRole.RejectRole)
            box.exec()
            b = box.clickedButton()
            if b is utf8:
                ed.encoding = "UTF-8"
                return encode_with(text, "UTF-8")
            if b is keep:
                return encode_with(text, ed.encoding, "replace")
            return None

    def save_editor(self, ed, force_dialog=False):
        path = ed.path
        if not path or force_dialog:
            start = ed.path or os.path.join(self._last_dir(), "Sin título.txt")
            path, flt = QFileDialog.getSaveFileName(
                self, "Guardar como", start, FILTER_SAVE)
            if not path:
                return False
            if not os.path.splitext(path)[1] and "*.txt" in flt:
                path += ".txt"
            self.settings.setValue("last_dir", os.path.dirname(path))
        text = ed.toPlainText().replace("\n", EOLS.get(ed.eol, "\n"))
        data = self._encode_for_save(ed, text)
        if data is None:
            return False
        self._unwatch(ed.path)
        try:
            with open(path, "wb") as f:
                f.write(data)
            ed.mtime = os.path.getmtime(path)
        except OSError as e:
            QMessageBox.warning(self, APP_NAME, f"No se pudo guardar:\n{e}")
            self._watch(ed.path)
            return False
        ed.path = path
        ed.document().setModified(False)
        self._watch(path)
        self.add_recent(path)
        self._update_title(ed)
        self.update_status()
        return True

    # ---------------- sesión ----------------
    def _session_file(self):
        return os.path.join(data_dir(), "session.json")

    def save_session(self):
        data = {"active": 0, "tabs": []}
        if not self._empty_session:
            data["active"] = self.tabbar.currentIndex()
            for i in range(self.tabbar.count()):
                ed = self.editor_at(i)
                mod = ed.document().isModified()
                data["tabs"].append({
                    "path": ed.path, "modified": mod, "eol": ed.eol,
                    "enc": ed.encoding,
                    "cursor": ed.textCursor().position(),
                    "text": ed.toPlainText() if (mod or not ed.path) else None,
                })
        try:
            with open(self._session_file(), "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False)
        except OSError:
            pass

    def _autosave_session(self):
        if self.owner and self.restore_session:
            self.save_session()

    def load_session(self):
        try:
            with open(self._session_file(), encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, ValueError):
            return
        for t in data.get("tabs", []):
            path, text = t.get("path"), t.get("text")
            if text is None:
                if not (path and os.path.exists(path)):
                    continue
                ed = self.open_path(path)
            else:
                ed = self.new_tab(text, path)
                ed.eol = t.get("eol", DEFAULT_EOL)
                ed.encoding = t.get("enc", "UTF-8")
                if path:
                    self._watch(path)
                    if os.path.exists(path):
                        ed.mtime = os.path.getmtime(path)
                ed.document().setModified(bool(t.get("modified")))
                self._update_title(ed)
            if ed is not None:
                cur = ed.textCursor()
                cur.setPosition(min(int(t.get("cursor", 0)),
                                    ed.document().characterCount() - 1))
                ed.setTextCursor(cur)
        n = self.tabbar.count()
        if n:
            self.tabbar.setCurrentIndex(
                max(0, min(int(data.get("active", 0)), n - 1)))

    # ---------------- edición ----------------
    def _edit_menu_show(self):
        ed = self.editor()
        if not ed:
            return
        sel = ed.textCursor().hasSelection()
        md = QApplication.clipboard().mimeData()
        self.a_undo.setEnabled(ed.document().isUndoAvailable())
        self.a_redo.setEnabled(ed.document().isRedoAvailable())
        for a in (self.a_cut, self.a_copy, self.a_delete, self.a_bing):
            a.setEnabled(sel)
        self.a_paste.setEnabled(bool(md and md.hasText()))
        self.a_goto.setEnabled(not self.wrap)

    def _edit_menu_hide(self):
        for a in self._edit_actions:
            a.setEnabled(True)

    def delete_sel(self):
        ed = self.editor()
        if ed:
            cur = ed.textCursor()
            cur.deleteChar()
            ed.setTextCursor(cur)

    def search_web(self):
        ed = self.editor()
        text = ed.textCursor().selectedText().replace(" ", " ") if ed \
            else ""
        text = text.strip()[:500]
        if text:
            QDesktopServices.openUrl(
                QUrl("https://www.bing.com/search?q=" + quote(text)))

    def find_step(self, backward):
        if not self.findbar.find_edit.text():
            self.findbar.open(False)
            return
        self.findbar.find(backward=backward)

    def goto_line(self):
        ed = self.editor()
        if not ed or self.wrap:
            return
        n, ok = QInputDialog.getInt(
            self, "Ir a la línea", "Número de línea:",
            ed.textCursor().blockNumber() + 1, 1, max(1, ed.blockCount()))
        if ok:
            ed.setTextCursor(QTextCursor(ed.document().findBlockByNumber(n - 1)))
            ed.centerCursor()

    def insert_datetime(self):
        ed = self.editor()
        if ed:
            ed.insertPlainText(
                QDateTime.currentDateTime().toString("h:mm AP d/M/yyyy"))

    def editor_menu(self, ed, gpos):
        m = QMenu(self)
        sel = ed.textCursor().hasSelection()
        md = QApplication.clipboard().mimeData()

        def add(text, slot, enabled=True, key=""):
            a = m.addAction(text + ("\t" + key if key else ""))
            a.setEnabled(enabled)
            a.triggered.connect(lambda _=False: slot())
            return a

        add("Deshacer", ed.undo, ed.document().isUndoAvailable(), "Ctrl+Z")
        m.addSeparator()
        add("Cortar", ed.cut, sel, "Ctrl+X")
        add("Copiar", ed.copy, sel, "Ctrl+C")
        add("Pegar", ed.paste, bool(md and md.hasText()), "Ctrl+V")
        add("Eliminar", self.delete_sel, sel, "Del")
        m.addSeparator()
        add("Seleccionar todo", ed.selectAll, True, "Ctrl+A")
        m.addSeparator()
        add("Buscar con Bing", self.search_web, sel, "Ctrl+E")
        m.addSeparator()
        r = m.addAction("Orden de lectura de derecha a izquierda")
        r.setCheckable(True)
        r.setChecked(ed.rtl)
        r.toggled.connect(ed.set_rtl)
        w = m.addAction("Mostrar espacios y tabulaciones")
        w.setCheckable(True)
        w.setChecked(ed.show_ws)
        w.toggled.connect(ed.set_show_whitespace)
        u = m.addMenu("Insertar carácter de control Unicode")
        for abbr, desc, ch in UNICODE_CONTROLS:
            u.addAction(f"{abbr}\t{desc}").triggered.connect(
                lambda _=False, c=ch: ed.insertPlainText(c))
        m.exec(gpos)

    # ---------------- formato / Markdown ----------------
    def md_wrap(self, left, right=None, placeholder=""):
        ed = self.editor()
        if not ed:
            return
        right = left if right is None else right
        cur = ed.textCursor()
        if cur.hasSelection():
            txt = cur.selectedText().replace(" ", "\n")
            n = len(left) + len(right)
            if (txt.startswith(left) and txt.endswith(right)
                    and len(txt) >= n and not (left == "*"
                                               and txt.startswith("**"))):
                cur.insertText(txt[len(left):len(txt) - len(right)])
            else:
                cur.insertText(left + txt + right)
        else:
            cur.insertText(left + placeholder + right)
            cur.movePosition(QTextCursor.MoveOperation.Left,
                             QTextCursor.MoveMode.MoveAnchor, len(right))
            cur.movePosition(QTextCursor.MoveOperation.Left,
                             QTextCursor.MoveMode.KeepAnchor, len(placeholder))
        ed.setTextCursor(cur)

    def md_link(self):
        ed = self.editor()
        if not ed:
            return
        url, ok = QInputDialog.getText(self, "Hipervínculo", "Dirección:",
                                       text="https://")
        if not ok or not url:
            return
        cur = ed.textCursor()
        txt = cur.selectedText().replace(" ", " ") or "texto"
        cur.insertText(f"[{txt}]({url})")
        ed.setTextCursor(cur)

    def md_prefix(self, make):
        ed = self.editor()
        if not ed:
            return
        cur = ed.textCursor()
        doc = ed.document()
        first = doc.findBlock(cur.selectionStart())
        last = doc.findBlock(cur.selectionEnd())
        if (cur.hasSelection() and cur.selectionEnd() == last.position()
                and last.blockNumber() != first.blockNumber()):
            last = last.previous()
        cur.beginEditBlock()
        b, i = first, 0
        while b.isValid():
            QTextCursor(b).insertText(make(i))
            i += 1
            if b.blockNumber() == last.blockNumber():
                break
            b = b.next()
        cur.endEditBlock()

    def md_heading(self, level):
        ed = self.editor()
        if not ed:
            return
        block = ed.textCursor().block()
        text = re.sub(r"^#{1,6}\s*", "", block.text())
        c = QTextCursor(block)
        c.movePosition(QTextCursor.MoveOperation.EndOfBlock,
                       QTextCursor.MoveMode.KeepAnchor)
        c.insertText(("#" * level + " " if level else "") + text)

    @staticmethod
    def _strip_md(t):
        t = re.sub(r"(?m)^\s{0,3}#{1,6}\s+", "", t)
        t = re.sub(r"(?m)^(\s*)([-*+]|\d+\.)\s+", r"\1", t)
        t = re.sub(r"\*\*(.+?)\*\*", r"\1", t)
        t = re.sub(r"__(.+?)__", r"\1", t)
        t = re.sub(r"(?<!\*)\*(?!\*)(.+?)\*", r"\1", t)
        t = re.sub(r"~~(.+?)~~", r"\1", t)
        t = re.sub(r"`(.+?)`", r"\1", t)
        return re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", t)

    def md_clear(self):
        ed = self.editor()
        if not ed:
            return
        cur = ed.textCursor()
        if not cur.hasSelection():
            cur.select(QTextCursor.SelectionType.BlockUnderCursor)
            cur = QTextCursor(ed.textCursor().block())
            cur.movePosition(QTextCursor.MoveOperation.EndOfBlock,
                             QTextCursor.MoveMode.KeepAnchor)
        txt = cur.selectedText().replace(" ", "\n")
        cur.insertText(self._strip_md(txt))
        ed.setTextCursor(cur)

    # ---------------- fuente / zoom / ajuste ----------------
    def _zoomed_font(self):
        f = QFont(self.font_)
        f.setPointSizeF(max(1.0, self.font_.pointSizeF() * self.zoom / 100))
        return f

    def _apply_font(self):
        f = self._zoomed_font()
        for ed in self.docs.values():
            ed.setFont(f)
        self.lbl_zoom.setText(f"{self.zoom}%")

    def choose_font(self):
        font, ok = QFontDialog.getFont(self.font_, self, "Fuente")
        if ok:
            self.font_ = font
            self.settings.setValue("font", font.toString())
            self._apply_font()

    def change_zoom(self, delta=0, reset=False):
        self.zoom = 100 if reset else max(10, min(500, self.zoom + delta))
        self.settings.setValue("zoom", self.zoom)
        self._apply_font()

    def set_wrap(self, on):
        self.wrap = bool(on)
        self.settings.setValue("wrap", self.wrap)
        for ed in self.docs.values():
            ed.set_wrap(self.wrap)

    # ---------------- barra de estado ----------------
    def update_status(self):
        ed = self.editor()
        if not ed:
            return
        cur = ed.textCursor()
        self.lbl_pos.setText(
            f"Ln {cur.blockNumber() + 1}, Col {cur.positionInBlock() + 1}")
        total = max(0, ed.document().characterCount() - 1)
        if cur.hasSelection():
            n = abs(cur.position() - cur.anchor())
            self.lbl_chars.setText(f"{n} de {total} caracteres")
        else:
            self.lbl_chars.setText(f"{total} caracteres")
        self.lbl_zoom.setText(f"{self.zoom}%")
        self.lbl_eol.setText(ed.eol)
        self.lbl_enc.setText(ed.encoding)

    def _popup_above(self, menu, label):
        pos = label.mapToGlobal(QPoint(0, 0))
        menu.exec(QPoint(pos.x(), pos.y() - menu.sizeHint().height()))

    def eol_menu(self):
        ed = self.editor()
        if not ed:
            return
        m = QMenu(self)
        grp = QActionGroup(m)
        for name in EOLS:
            a = m.addAction(name)
            a.setCheckable(True)
            a.setChecked(ed.eol == name)
            grp.addAction(a)
            a.triggered.connect(lambda _=False, n=name: self.set_eol(n))
        self._popup_above(m, self.lbl_eol)

    def set_eol(self, name):
        ed = self.editor()
        if ed and ed.eol != name:
            ed.eol = name
            ed.document().setModified(True)
            self.update_status()

    def enc_menu(self):
        ed = self.editor()
        if not ed:
            return
        m = QMenu(self)
        reopen = m.addMenu("Volver a abrir con codificación")
        reopen.setEnabled(bool(ed.path))
        save = m.addMenu("Guardar con codificación")
        for enc in ENCODINGS:
            reopen.addAction(enc).triggered.connect(
                lambda _=False, e=enc: self.reopen_with(e))
            a = save.addAction(enc)
            a.setCheckable(True)
            a.setChecked(ed.encoding == enc)
            a.triggered.connect(lambda _=False, e=enc: self.set_encoding(e))
        self._popup_above(m, self.lbl_enc)

    def set_encoding(self, enc):
        ed = self.editor()
        if ed and ed.encoding != enc:
            ed.encoding = enc
            ed.document().setModified(True)
            self.update_status()

    def reopen_with(self, enc):
        ed = self.editor()
        if not ed or not ed.path:
            return
        if ed.document().isModified():
            r = QMessageBox.question(
                self, APP_NAME,
                "Se perderán los cambios sin guardar. ¿Continuar?")
            if r != QMessageBox.StandardButton.Yes:
                return
        self.reload_editor(ed, enc)

    # ---------------- imprimir ----------------
    def _load_page_layout(self):
        s = self.settings
        idx = s.value("page_paper", 0, type=int)
        idx = idx if 0 <= idx < len(PAPERS) else 0
        land = s.value("page_land", False, type=bool)
        mg = [s.value(f"page_m{k}", 20.0, type=float) for k in "ltrb"]
        lay = QPageLayout(
            QPageSize(PAPERS[idx][1]),
            QPageLayout.Orientation.Landscape if land
            else QPageLayout.Orientation.Portrait,
            QMarginsF(*mg), QPageLayout.Unit.Millimeter)
        return lay if lay.isValid() else default_page_layout()

    def _save_page_layout(self):
        s = self.settings
        lay = self.page_layout
        for i, (_n, pid) in enumerate(PAPERS):
            if lay.pageSize().id() == pid:
                s.setValue("page_paper", i)
        s.setValue("page_land",
                   lay.orientation() == QPageLayout.Orientation.Landscape)
        m = lay.margins(QPageLayout.Unit.Millimeter)
        for k, v in zip("ltrb", (m.left(), m.top(), m.right(), m.bottom())):
            s.setValue(f"page_m{k}", v)
        s.setValue("print_header", self.header)
        s.setValue("print_footer", self.footer)

    def page_setup(self):
        dlg = PageSetupDialog(self, self.page_layout, self.header, self.footer)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            lay = dlg.result_layout()
            if lay.isValid():
                self.page_layout = lay
            self.header = dlg.header.text()
            self.footer = dlg.footer.text()
            self._save_page_layout()

    def print_dialog(self):
        ed = self.editor()
        if not ed:
            return
        printer = QPrinter(QPrinter.PrinterMode.HighResolution)
        printer.setPageLayout(self.page_layout)
        dlg = QPrintDialog(printer, self)
        dlg.setOption(QPrintDialog.PrintDialogOption.PrintSelection,
                      ed.textCursor().hasSelection())
        if dlg.exec() == QDialog.DialogCode.Accepted:
            self.print_editor(
                ed, printer,
                printer.printRange() == QPrinter.PrintRange.Selection)

    def _hf_parts(self, s, ed, page):
        parts = {"l": "", "c": "", "r": ""}
        cur, i = "c", 0
        while i < len(s):
            ch = s[i]
            if ch == "&" and i + 1 < len(s):
                code = s[i + 1]
                i += 2
                lc = code.lower()
                if code == "&":
                    parts[cur] += "&"
                elif lc == "f":
                    parts[cur] += ed.name()
                elif lc == "p":
                    parts[cur] += str(page)
                elif lc == "d":
                    parts[cur] += QDate.currentDate().toString("dd/MM/yyyy")
                elif lc == "t":
                    parts[cur] += QTime.currentTime().toString("HH:mm")
                elif lc in ("l", "c", "r"):
                    cur = lc
                continue
            parts[cur] += ch
            i += 1
        return parts

    def _draw_hf(self, painter, s, ed, page, rect):
        if not s:
            return
        parts = self._hf_parts(s, ed, page)
        for key, al in (("l", Qt.AlignmentFlag.AlignLeft),
                        ("c", Qt.AlignmentFlag.AlignHCenter),
                        ("r", Qt.AlignmentFlag.AlignRight)):
            if parts[key]:
                painter.drawText(
                    rect, parts[key],
                    QTextOption(al | Qt.AlignmentFlag.AlignVCenter))

    def print_editor(self, ed, printer, selection_only=False):
        text = (ed.textCursor().selectedText().replace(" ", "\n")
                if selection_only else ed.toPlainText())
        font = QFont(self.font_)
        doc = QTextDocument()
        doc.setDefaultFont(font)
        opt = QTextOption()
        opt.setWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
        doc.setDefaultTextOption(opt)
        doc.setPlainText(text)
        layout = doc.documentLayout()
        layout.setPaintDevice(printer)
        res = printer.resolution()
        pr = printer.pageLayout().paintRectPixels(res)
        width, height = float(pr.width()), float(pr.height())
        fm = QFontMetricsF(font, printer)
        hf_h = fm.height() * 2
        top = hf_h if self.header else 0.0
        bottom = hf_h if self.footer else 0.0
        body_h = height - top - bottom
        doc.setPageSize(QSizeF(width, body_h))
        painter = QPainter()
        if not painter.begin(printer):
            return False
        for page in range(max(1, doc.pageCount())):
            if page:
                printer.newPage()
            painter.save()
            painter.translate(0, top - page * body_h)
            ctx = QAbstractTextDocumentLayout.PaintContext()
            ctx.clip = QRectF(0, page * body_h, width, body_h)
            layout.draw(painter, ctx)
            painter.restore()
            painter.setFont(font)
            self._draw_hf(painter, self.header, ed, page + 1,
                          QRectF(0, 0, width, hf_h))
            self._draw_hf(painter, self.footer, ed, page + 1,
                          QRectF(0, height - hf_h, width, hf_h))
        painter.end()
        return True

    # ---------------- cierre / arrastrar y soltar ----------------
    def closeEvent(self, e):
        if self.owner and self.restore_session:
            self.save_session()
        else:
            for ed in list(self.docs.values()):
                if not self.maybe_save(ed):
                    e.ignore()
                    return
            if self.owner:
                self._empty_session = True
                self.save_session()
        self.settings.setValue("geometry", self.saveGeometry())
        e.accept()

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dropEvent(self, e):
        paths = [u.toLocalFile() for u in e.mimeData().urls()
                 if u.isLocalFile()]
        if paths:
            self.open_paths(paths)
            e.acceptProposedAction()


def main():
    global SYS_PALETTE
    args = sys.argv[1:]
    new_session = "--new" in args
    files = [a for a in args if not a.startswith("--")]
    app = QApplication([sys.argv[0]])
    app.setApplicationName(APP_NAME)
    app.setDesktopFileName("notepad")
    SYS_PALETTE = app.palette()
    win = Notepad(files, new_session)
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
