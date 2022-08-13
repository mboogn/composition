
from dis import opmap, opname, COMPILER_FLAG_NAMES
from types import FunctionType
from itertools import chain, filterfalse

from types import FunctionType, CodeType
from itertools import chain, filterfalse

def get_code(x):
    "Returns the code attribute of x.  Methodology copied and altered from the dis module."
    if isinstance(x, CodeType): return x
    # Extract functions from methods.
    x = getattr(x, '__func__', x)
    # Extract compiled code objects from...
    #x = getattr(x, '__code__', 0) or getattr(x, 'gi_code', 0) or getattr(x, 'ag_code', 0) or getattr(x, 'cr_code', x)
    # ...lambda || function,  #...or generator object,  #...or asynchronous generator object  #...or coroutine.
    return getattr(x, '__code__', 0) \
           or getattr(x, 'gi_code', 0) \
           or getattr(x, 'ag_code', 0) \
           or getattr(x, 'cr_code', x)


code_co_varnames = ("co_name", "co_code", "co_lnotab", 
    "co_firstlineno", "co_filename", "co_stacksize", "co_flags", 
    "co_nlocals", "co_argcount", "co_posonlyargcount", "co_kwonlyargcount", 
    "co_names", "co_varnames", "co_consts", "co_cellvars", "co_freevars")
def get_co_dict(fcode, as_itemgen=False):
    "returns a dictionary or a key-value-pair generator of the co_-prefixed code attributes of object ‘fcode’"
    fcode = get_code(fcode)
    if as_itemgen: return ((ky, getattr(fcode, ky)) for ky in code_co_varnames)
    return {ky: getattr(fcode, ky) for ky in code_co_varnames}


co_flags_map = {v: k for k, v in COMPILER_FLAG_NAMES.items()}

_getcocoflags = lambda f: getattr(get_code(f), 'co_flags', None)
_g_flagcheck = lambda x: x.__and__

_isoptimized = _g_flagcheck(co_flags_map['OPTIMIZED'])
_has__⃰args = _g_flagcheck(co_flags_map["VARARGS"])
_has__⃰_⃰kwargs = _g_flagcheck(co_flags_map['VARKEYWORDS'])
_isnested = _g_flagcheck(co_flags_map['NESTED'])
_isgenerator = _g_flagcheck(co_flags_map['GENERATOR'])
_iscoroutine = _g_flagcheck(co_flags_map['COROUTINE'])
_is_iterable_coroutine = _g_flagcheck(co_flags_map['ITERABLE_COROUTINE'])
_is_async_generator = _g_flagcheck(co_flags_map['ASYNC_GENERATOR'])

def is_not_iteratorlike(f):
    flgs = _getcocoflags(f)
    return not (_isgenerator(flgs) or _iscoroutine(flgs) or _is_iterable_coroutine(flgs) \
        or _is_async_generator(flgs))


_bc_loadconst = opmap['LOAD_CONST']
_bc_loadvar = opmap['LOAD_FAST']
_bc_storevar = opmap['STORE_FAST']
_bc_deletevar = opmap['DELETE_FAST']
_bc_return = opmap['RETURN_VALUE']
_bcs_jrel = tuple(map(opmap.__getitem__, ['JUMP_IF_FALSE_OR_POP', 'JUMP_IF_TRUE_OR_POP', 'POP_JUMP_IF_FALSE', 'POP_JUMP_IF_TRUE', 'JUMP_FORWARD']))
_bc_foriter = opmap["FOR_ITER"]
try:
    bcv_genstart = opmap['GEN_START']
except KeyError:
    bcv_genstart = opmap["FOR_ITER"]

_bcs_var = _bc_loadvar, _bc_storevar, _bc_deletevar


def rearrange_argorder(f: FunctionType, reordering=(0, 1, 2), fcode=None, replace=False, name=None):
    "Changes internal order of operations:  \n"\
    "    rearrange_argorder(lambda x, y, z: (x - y - z), reordering=(2, 1, 0))  →  lambda x, y, z: (z - y - x)"
    if fcode is None:
        fcode = get_code(f)
    
    fbytecode = list(fcode.co_code)
    fdefaults = f.__defaults__
    #fkwdefaults = f.__kwdefaults__
    
    for i, byt in enumerate(fbytecode):
        if byt in _bcs_var:
            v_id = fbytecode[i + 1]
            fbytecode[i + 1] = reordering[v_id]
    
    if fdefaults:
        ln = len(reordering)
        while len(fdefaults) < ln:
            fdefaults = (None,) + fdefaults
        fdefaults = tuple(map(fdefaults.__getitem__, reordering))
    
    if replace:
        if name:
            f.__name__ = name
            f.__code__ = fcode.replace(co_code=bytes(fbytecode), co_name=name)
        else:
            f.__code__ = fcode.replace(co_code=bytes(fbytecode))
        f.__defaults__ = fdefaults
        return  f
    
    name = name or '<h>'
    return FunctionType(code=fcode.replace(co_code=bytes(fbytecode), co_name=name), \
    globals=f.__globals__, name=name, argdefs=fdefaults, closure=f.__closure__)


def compose(f: FunctionType, g: FunctionType, name=None, argorder: tuple=None, **kwg) -> FunctionType:
    
    if argorder:
        f = rearrange_argorder(f, reordering=argorder, replace=kwg.get("disposable", False), name=None)
    
    fcode = get_code(f)
    gcode = get_code(g)
    if is_not_iteratorlike(fcode) and is_not_iteratorlike(gcode):
        fnargs = fcode.co_argcount
        gnargs = gcode.co_argcount
        if 0==fnargs==gnargs==1:
            return _compose_fx_gx_fgx(f, g, fcode, gcode, name)
        if fnargs >= 1 <= gnargs:
            return _compose_fxy_gxy_fgxyz(f, g, fcode, gcode, name, fnargs=fnargs, gnargs=gnargs, **kwg)
    raise ValueError("invalid inputs")


def _compose_fx_gx_fgx(f, g, fcode=None, gcode=None, name=None):
    "Returns f(g(x))"
    if None is fcode or None is gcode:
        fcode = get_code(f)
        gcode = get_code(g)
        
    fbytecode = tuple(fcode.co_code)
    gbytecode = gcode.co_code
    
    fco_dict = get_co_dict(fcode)
    gco_dict = get_co_dict(gcode)
    hco_dict = {}
    
    fbctup = tuple(fbytecode)
    gbctup = tuple(gbytecode)
    fnvarloads = fbctup.count(_bc_loadvar)
    gnvarloads = gbctup.count(_bc_loadvar)
    fnvarsaves = fbctup.count(_bc_storevar)
    gnvarsaves = gbctup.count(_bc_storevar)
    
    if fnvarloads > 1:
        fbytecode = (_bc_storevar, 0) + fbytecode#.replace(bytes((_bc_loadvar, 0)), bytes((_bc_loadvar, 1)))
        #gco_dict['co_nlocals'] += 1
    for ky, gvl in gco_dict.items():
        if ky=='co_name':
            continue
        if type(gvl) is tuple:
            if ky == 'co_consts':
                
                oldfvl = fco_dict[ky]
                hco_dict[ky] = newvl = tuple(chain(gvl, filterfalse(gvl.__contains__, oldfvl[1:])))
                
                if gvl[0] and oldfvl[0]:    # Splice docstring<
                    hco_dict[ky] = newvl = (gvl[0]+oldfvl[0], ) + newvl[1:]
                    
                fbytecode = list(fbytecode)
                
                for i, byt in enumerate(fbytecode):
                    if byt == _bc_loadconst:    # fix const references in bytecode
                        argbyt = fbytecode[i + 1]
                        fbytecode[i + 1] = newvl.index(oldfvl[argbyt])
                    
                fbytecode = bytes(fbytecode)
                continue
            if ky == 'co_varnames':
                continue
            hco_dict[ky] = gvl + fco_dict[ky]
    
    hbytecode = gcode.co_code.replace(bytes((_bc_return, 0)), fbytecode)
    name = name or '<h>'
    hcode = fcode.replace(co_code=hbytecode, co_name=name, **hco_dict)
    return FunctionType(code=hcode, globals=g.__globals__ | f.__globals__, name=name, \
    argdefs=g.__defaults__, closure=f.__closure__)


def _compose_fxy_gxy_fgxyz(f, g, fcode=None, gcode=None, name=None, **kwg):
    "Returns f(g(x, y), z)."
    if None is fcode or None is gcode:
        fcode = get_code(f)
        gcode = get_code(g)
    
    argtypecode = kwg.get('argtypecode', 0)
    
    fnargs = kwg.get('fnargs', None) or fcode.co_argcount
    gnargs = kwg.get('gnargs', None) or gcode.co_argcount
    
    #fdefs, fkwdefs = f.__defaults__, f.__kwdefaults__
    #gdefs, gkwdefs = g.__defaults__, g.__kwdefaults__
    #↑#↑#↑# (later)
    
    newnlocals = newnargs = gnargs+fnargs-(gnargs and fnargs and 1)
    if argtypecode==1:
        newnargs = fnargs if fnargs>=gnargs else gnargs
        print(newnargs)
    if gcode.co_nlocals > gnargs or fcode.co_nlocals > fnargs:
        newnlocals = gcode.co_nlocals + fcode.co_nlocals - (gnargs + fnargs) + newnargs
    
    newname = name or '<h>'
    newflags = gcode.co_flags | fcode.co_flags
    newvarnames = tuple(map(chr, range(97, 97 + newnargs)))
    
    fbytecode = tuple(fcode.co_code)[2:]
    gbytecode = gcode.co_code
    
    fco_dict = get_co_dict(fcode)
    gco_dict = get_co_dict(gcode)
    hco_dict = {'co_nlocals': newnlocals, 'co_argcount': newnargs, 'co_name': newname, \
    'co_flags': newflags, 'co_varnames': newvarnames}
    hco_dict |= kwg.pop('co_overrides', {})
    
    #fstarred = starred(f)
#    gstarred = starred(g)
#    hpogstarred = fstarred[0] or gstarred[0]
#    hkwgstarred = fstarred[1] or gstarred[1]
    
    #fbctup = tuple(fbytecode)}
#    gbctup = tuple(gbytecode)
#    fnvarloads = fbctup.count(_bc_loadvar)
#    #gnvarloads = gbctup.count(_bc_loadvar)
#    fnvarsaves = fbctup.count(_bc_storevar)
#    #gnvarsaves = gbctup.count(_bc_storevar)
#    #fnreturns = fbctup.count(_bc_return)
#   gnreturns = gbctup.count(_bc_return)
    
    fbytecode = list(fbytecode)
    
    for ky, gvl in gco_dict.items():
        
        if type(gvl) is tuple:
            oldfvl = fco_dict[ky]
            
            if ky=='co_varnames':
                delta = gnargs - (gnargs and 1)
                if argtypecode==1:
                    delta = 0
                for i, byt in enumerate(fbytecode):
                    if byt == _bc_loadvar:    # fix arg references in bytecode
                        argbyt = fbytecode[i + 1]
                        fbytecode[i + 1] = argbyt + delta
                continue
            if ky == 'co_consts':
                hco_dict[ky] = newvl = tuple(chain(gvl, filterfalse(gvl.__contains__, oldfvl[1:])))
                
                if gvl[0] and oldfvl[0]:    # Splice docstring
                    hco_dict[ky] = newvl = (gvl[0]+oldfvl[0], ) + newvl[1:]
                
                for i, byt in enumerate(fbytecode):
                    if byt == _bc_loadconst:    # fix const references in bytecode
                        argbyt = fbytecode[i + 1]
                        fbytecode[i + 1] = newvl.index(oldfvl[argbyt])
            
            #hco_dict[ky] = tuple(chain(gvl, filterfalse(gvl.__contains__, oldfvl)))
            #gvl + fco_dict[ky]
    
    fbytecode = bytes(fbytecode)
    hbytecode = gcode.co_code.replace(bytes((_bc_return, 0)), fbytecode)
    hfstart = hbytecode.index(fbytecode)
    
    hbytecode = list(hbytecode)
    for i, byt in enumerate(hbytecode):
        if i < hfstart:
            continue
        if byt in _bcs_jrel:
            argbyt = hbytecode[i + 1]
            hbytecode[i + 1] = argbyt + hfstart
    hco_dict['co_code'] = hbytecode = bytes(hbytecode)
    
    hcode = fcode.replace(**hco_dict)
    h = FunctionType(code=hcode, globals=g.__globals__ | f.__globals__, name=name, \
    argdefs=kwg.get('__defaults__', g.__defaults__), closure=kwg.get('__closure__', f.__closure__) or ())
    h.__kwdefaults__ = kwg.get('__kwdefaults__', {})
    h.__annotations__ = kwg.get('__annotations__', {})
    return h


if __name__ == "__main__":
    
    
    f = lambda x, y: x - y
    g = lambda x, y: x / y
    
    h = compose(f, g)
    
    x, y = 5,6
    z = 5
    print(h(x, y, z), f(x, g(y, z)), f(g(x, y), z))
    
    f.__defaults__ = 0, 1
    f_ = rearrange_argorder(f, (1, 0), replace=False)
    
    h = compose(f_, g)
    h = rearrange_argorder(h, (0, 1, 2))
    
    print(h(x, y, z), f(x, g(y, z)), f(g(x, y), z), '\n', h.__defaults__)
    
    h2 = compose(h, h)
    print(*get_co_dict(h2).items(), sep='\n')


