// File foreign.js
// Round toward zero by default
function round(a)
{
    if (a < 0)
        return Math.ceil(a);
    else
        return Math.floor(a);
}


function evaluate_expression(expression, evaluated)
{
    expression = deref(expression);
    if (TAG(expression) == TAG_INT)
    {
        if ((VAL(expression) & (1 << (WORD_BITS-1))) == (1 << (WORD_BITS-1)))
            evaluated.value = VAL(expression) - (1 << WORD_BITS);
        else
            evaluated.value = VAL(expression);
        return true;
    }
    if (TAG(expression) == TAG_FLT)
    {
        evaluated.value = floats[VAL(expression)];
        return true;
    }
    if (TAG(expression) == TAG_REF)
    {
        return instantiation_error(expression);
    }
    else if (TAG(expression) == TAG_ATM && expression == lookup_atom("pi"))
    {
        evaluated.value = Math.PI;
        return true;
    }
    else if (TAG(expression) == TAG_STR)
    {
        var v = [];
        var value = 0;
        var arity = ftable[VAL(memory[VAL(expression)])][1];
        var name = atable[ftable[VAL(memory[VAL(expression)])][0]];
        for (var i = 0; i < arity; i++)
        {
            var t = {};
            if (!evaluate_expression(memory[VAL(expression)+i+1], t))
                return false;
            else
                v[i] = t.value;
        }
        if (name == "+" && arity == 2)
            evaluated.value = v[0] + v[1];
        else if (name == "-" && arity == 2)
            evaluated.value = v[0] - v[1];
        else if (name == "*" && arity == 2)
            evaluated.value = v[0] * v[1];
        else if (name == "//" && arity == 2)
            evaluated.value = ~~(v[0] / v[1]);
        else if (name == "/" && arity == 2)
            evaluated.value = v[0] / v[1];
        else if (name == "rem" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");
            evaluated.value = v[0] - (round(v[0]/v[1]) * v[1]);            
        }
        else if (name == "mod" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");            
            evaluated.value = v[0] - (Math.floor(v[0]/v[1]) * v[1]);
        }
        else if (name == "-" && arity == 1)
            evaluated.value = -v[0];
        else if (name == "abs" && arity == 1)
            evaluated.value = Math.abs(v[0]);
        else if (name == "sign" && arity == 1)
        {
            if (v[0] == 0)
                evaluated.value = 0;
            else if (v[0] > 0)
                evaluated.value = 1;
            else
                evaluated.value = -1;
        }
        else if (name == "float_integer_part" && arity == 1)
            evaluated.value = ~~v[0];
        else if (name == "float_fractional_part" && arity == 1)
            evaluated.value = v[0] % 1;
        else if (name == "float" && arity == 1)
            evaluated.value = v[0];
        else if (name == "floor" && arity == 1)
            evaluated.value = Math.floor(v[0]);
        else if (name == "truncate" && arity == 1)
            evaluated.value = ~~v[0];
        else if (name == "round" && arity == 1)
            evaluated.value = Math.round(v[0]);
        else if (name == "ceiling" && arity == 1)
            evaluated.value = Math.ceil(v[0]);
        else if (name == "**" && arity == 2)
            evaluated.value = Math.pow(v[0], v[1]);
        else if (name == "sin" && arity == 1)
            evaluated.value = Math.sin(v[0]);
        else if (name == "cos" && arity == 1)
            evaluated.value = Math.cos(v[0]);
        else if (name == "atan" && arity == 1)
            evaluated.value = Math.atan(v[0]);
        else if (name == "exp" && arity == 1)
            evaluated.value = Math.exp(v[0]);
        else if (name == "log" && arity == 1)
            evaluated.value = Math.log(v[0]);
        else if (name == "sqrt" && arity == 1)
            evaluated.value = Math.sqrt(v[0]);
        else if (name == ">>" && arity == 2)
            evaluated.value = v[0] >> [v1];
        else if (name == "<<" && arity == 2)
            evaluated.value = v[0] << [v1];
        else if (name == "/\\" && arity == 2)
            evaluated.value = v[0] & [v1];
        else if (name == "\\/" && arity == 2)
            evaluated.value = v[0] | [v1];
        else if (name == "\\" && arity == 1)
            evaluated.value = ~v[0];
        // Corrigendum
        else if (name == "+" && arity == 1)
            evaluated.value = v[0];
        else if (name == "max" && arity == 2)
            evaluated.value = Math.max(v[0], v[1]);
        else if (name == "min" && arity == 2)
            evaluated.value = Math.min(v[0], v[1]);
        else if (name == "acos" && arity == 2)
            evaluated.value = Math.acos(v[0], v[1]);
        else if (name == "asin" && arity == 2)
            evaluated.value = Math.asin(v[0], v[1]);
        else if (name == "tan" && arity == 2)
            evaluated.value = Math.tan(v[0], v[1]);
        else if (name == "xor" && arity == 2)
            evaluated.value = v[0] ^ v[1];
        else if (name == "atan2" && arity == 2)
            evaluated.value = Math.atan2(v[0], v[1]);
        else if (name == "^" && arity == 2)
            evaluated.value = Math.pow(v[0], v[1]);
        else if (name == "div" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");
            evaluated.value = round(v[0] /v[1]);        
        }
        else
        {
            var indicator = state.H ^ (TAG_STR << WORD_BITS);
            memory[state.H++] = lookup_functor("/", 2);
            memory[state.H++] = lookup_atom(name);
            memory[state.H++] = arity ^ (TAG_INT << WORD_BITS);
            return type_error("evaluable", indicator)
        }
        return true;            
    }
    else if (TAG(expression) == TAG_ATM)
    {
        var indicator = state.H ^ (TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor("/", 2);
        memory[state.H++] = expression;
        memory[state.H++] = 0 ^ (TAG_INT << WORD_BITS);
        return type_error("evaluable", indicator)
    }
    else if (TAG(expression) == TAG_STR)
    {
        return type_error("evaluable", expression);
    }
    abort("Illegal type");
    return {status:0};
}

function term_from_list(list, tail)
{
    var tmp = state.H;
    for (var i = 0; i < list.length; i++)
    {
        alloc_list();
        memory[state.H++] = list[i];        
    }
    memory[state.H++] = tail;
    return memory[tmp];
}

function predicate_fail()
{
    return false;
}

function predicate_true()
{
    return true;
}


function predicate_is(value, expression)
{
    var e = {};
    if (!evaluate_expression(expression, e))
        return false;
//    if (e.status)
//    else
    // Note that e.value may be negative. Have to AND to get rid of any high bits
    if (e.value == ~~e.value)
    {
        // FIXME: Is this right?! This just truncates to WORD_BITS bits!
        e.value &= ((1 << WORD_BITS) -1);
        return (e.status != 0 && unify(e.value ^ (TAG_INT << WORD_BITS), value));
    }
    else
    {
        return (e.status != 0 && unify(lookup_float(e.value), value));
    }
}


function predicate_ne(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value != be.value;
    return false;
}

function predicate_gt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value > be.value;
    return false;
}

function predicate_lt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value < be.value;
    return false;
}

function predicate_elt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value <= be.value;
    return false;
}

function predicate_egt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
    {
        debug(ae.value + " >= " + be.value);
        return ae.value >= be.value;
    }
    return false;
}


function predicate_eq(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value == be.value;
    return false;
}

function predicate_term_variables(t, vt)
{    
    return unify(term_from_list(term_variables(t), NIL), vt);
}

function term_variables(z)
{
    var pdl = [z];
    var vars = [];
    while (pdl.length != 0)
    {
        var t = deref(pdl.pop());
        if (TAG(t) == TAG_REF)
        {
            if (vars.indexOf(t) == -1)
            {
                vars.push(t);
            }
        }
        else if (TAG(t) == TAG_LST)
        {
            pdl.push(memory[VAL(t)+1]);
            pdl.push(memory[VAL(t)]);
        }
        else if (TAG(t) == TAG_STR)
        {
            ftor = VAL(memory[VAL(t)]);
            for (var i = ftable[ftor][1]-1; i >= 0 ; i--)
                pdl.push(memory[VAL(t) + 1 + i]);
        }
    }
    return vars;
}

function writeln(t)
{
    stdout(format_term(t, {numbervars: true, ignore_ops: false, quoted:false}) + "\n");
    return true;
}

function predicate_halt(n)
{
    state.running = false;
    return true;
}

function predicate_univ(term, list_term)
{
    if (term & M_BIT)
        abort("GC exception: M bit is still set");
    switch(TAG(term))
    {
    case TAG_ATM:
    case TAG_INT:
    case TAG_FLT:
        var list = term_from_list([term], NIL);
        return unify(list_term, list);
    case TAG_REF:
        // Save space on heap for ftor
        var tmp = state.H;
        state.H++;
        var arity = 0;
        if (TAG(list_term) != TAG_LST)
            return type_error("list", list_term);
        if (TAG(deref(memory[VAL(list_term)])) != TAG_ATM)
            return type_error("atom", deref(memory[VAL(list_term)]));
        var ftor_name = atable[VAL(deref(memory[VAL(list_term)]))];
        list_term = memory[VAL(list_term)+1];
        // Now write the args
        while (TAG(list_term) == TAG_LST)
        {
            // Write head
            memory[state.H++] = memory[VAL(list_term)];
            // Update tail
            list_term = memory[VAL(list_term)+1];
            arity++;
        }
        // Check tail
        if (list_term != NIL)
        {
            if (TAG(list_term) == TAG_REF)
                return instantiation_error(list_term);
            else
                return type_error("list", list_term);
        }
        memory[tmp] = lookup_functor(ftor_name, arity);
        return unify(term, tmp ^ (TAG_STR << WORD_BITS));
    case TAG_STR:
        var ftor = VAL(memory[VAL(term)]);
        if (ftable[ftor] === undefined)
            abort("Garbage functor " + hex(ftor) + " pointed at by " + hex(term));
        var list = [ftable[ftor][0] ^ (TAG_ATM << WORD_BITS)];
        for (var i = 0; i < ftable[ftor][1]; i++)
        {
            list.push(memory[VAL(term)+1+i]);
        }
        return unify(list_term, term_from_list(list, NIL));
    case TAG_LST:
        var list = [lookup_atom(".")];
        list.push(memory[VAL(term)]);
        list.push(memory[VAL(term)+1]);
        return unify(list_term, term_from_list(list, NIL));
    }
}

function predicate_functor(term, name, arity)
{
    switch(TAG(term))
    {
    case TAG_REF:
        if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
        {
            var name_string = atable[VAL(name)];
            var ftor = lookup_functor(name_string, VAL(arity));
            var t = state.H ^ (TAG_STR << WORD_BITS);
            memory[state.H++] = ftor;
            for (i = 0; i < VAL(arity); i++)
                alloc_var();
            return unify(term, t);
        }
        else if (TAG(name) == TAG_REF)
            return instantiation_error(name);
        else if (TAG(arity) == TAG_REF)
            return instantiation_error(arity);
        else if (TAG(name) != TAG_ATM)
            return type_error("atom", name);
        else if (TAG(arity) != TAG_INT)
            return type_error("integer", arity);
    case TAG_ATM:
    case TAG_INT:
    case TAG_FLT:
        return unify(name, term) && unify(arity, 0 ^ (TAG_INT << WORD_BITS));        
    case TAG_STR:
        var ftor = VAL(memory[VAL(term)]);
        return unify(name, ftable[ftor][0] ^ (TAG_ATM << WORD_BITS)) && unify(arity, ftable[ftor][1] ^ (TAG_INT << WORD_BITS));
    case TAG_LST:
        return unify(name, NIL) && unify(arity, 2 ^ (TAG_INT << WORD_BITS));        
    }
}

function predicate_arg(n, t, a)
{
    if (TAG(n) == TAG_REF)
        return instantiation_error(n);
    if (TAG(t) == TAG_REF)
        return instantiation_error(t);
    if (TAG(n) != TAG_INT)
        return type_error("integer", n);
    if (TAG(t) != TAG_STR)
        return type_error("compound", t);
    if (VAL(n) < 0)
        return domain_error("not_less_than_zero", n);
    var ftor = VAL(memory[VAL(t)]);
    if (VAL(n) == 0 || VAL(n) > ftable[ftor][1])
        return false;
    return unify(memory[VAL(t) + VAL(n)], a);
}

function predicate_var(v)
{
    return TAG(v) == TAG_REF;
}

function predicate_atom(v)
{
    return TAG(v) == TAG_ATM;
}

function predicate_integer(v)
{
    return TAG(v) == TAG_INT;
}

function predicate_float(v)
{
    return TAG(v) == TAG_FLT;
}

function predicate_compound(v)
{
    return TAG(V) == TAG_STR;
}

function predicate_ground(x)
{
    var args = [x];
    while(args.length > 0)
    {
        arg = args.pop();
        switch (TAG(arg))
        {
        case TAG_REF:
            return false;
        case TAG_INT:
        case TAG_FLT:
        case TAG_ATM:
            return true;
        case TAG_LST:
            args.push(memory[VAL(arg)]);
            args.push(memory[VAL(arg)+1]);
            continue;
        case TAG_STR:
            ftor = VAL(memory[VAL(arg)]);
            for (i = 0; i < ftable[ftor][1]; i++)
                args.push(memory[VAL(arg)+1+i]);
            continue;        
        }
    }
}

function predicate_unify(a, b)
{
    return unify(a,b);
}

function predicate_match(a, b)
{
    var match_pdl = [];
    match_pdl.push(a);
    match_pdl.push(b);
    while (match_pdl.length != 0)
    {
        var d1 = deref(match_pdl.pop());
        var d2 = deref(match_pdl.pop());
        if (d1 != d2)
        {
            type1 = TAG(d1);
            val1 = VAL(d1);
            type2 = TAG(d2);
            val2 = VAL(d2);          
            // If either is a variable or atomic then they must be equal in order to match. They are not equal if we get to this line, so bail.
            if (type1 == TAG_REF || type2 == TAG_REF || type2 == TAG_ATM || type2 == TAG_INT || type2 == TAG_FLT)
                return false;

            if (type1 != type2) // Types must be equal for matching
                return false;

            if (type1 == TAG_LST)
            {                        
                match_pdl.push(memory[val1]); // unify heads
                match_pdl.push(memory[val2]);
                match_pdl.push(memory[val1+1]); // unify tails
                match_pdl.push(memory[val2+1]);
            }
            else if (type1 == TAG_STR)
            {
                f1 = VAL(memory[val1]);
                f2 = VAL(memory[val2]);
                if (f1 == f2)
                {
                    for (var i = 0; i < ftable[f1][1]; i++)
                    {
                        match_pdl.push(val1 + 1 + i);
                        match_pdl.push(val2 + 1 + i);
                    }
                }
                else
                    return false;
            }
            else
                abort("Illegal tag");
        }
    }
    return true;
}

// gets the i-th arg of a term. First arg is index=1, not index=0.
function get_arg(term, index)
{
    return deref(memory[VAL(term) + index]);
}

function lookup_atom(name)
{
    var i;
    for (i = 0; i < atable.length; i++)
    {
        if (atable[i] == name)
            return i ^ (TAG_ATM << WORD_BITS);
    }
    i = atable.length;
    atable[i] = name;
    return i ^ (TAG_ATM << WORD_BITS);
}

function lookup_functor(name, arity) 
{
    var a = VAL(lookup_atom(name));
    var i;
    for (i = 0; i < ftable.length; i++)
        if (ftable[i][0] == a && ftable[i][1] == arity)
            return i ^ (TAG_ATM << WORD_BITS);
    i = ftable.length;
    ftable[i] = [a, arity];
    return i ^ (TAG_ATM << WORD_BITS);    
}


/* Memory files */
var memory_files = [];

function toByteArray(str)
{
    var byteArray = [];
    for (var i = 0; i < str.length; i++)
    {
        if (str.charCodeAt(i) <= 0x7F)
        {
            byteArray.push(str.charCodeAt(i));
        }
        else 
        {
            var h = encodeURIComponent(str.charAt(i)).substr(1).split('%');
            for (var j = 0; j < h.length; j++)
            {
                byteArray.push(parseInt(h[j], 16));
            }
        }
    }
    return byteArray;
}

function JSfromByteArray(byteArray)
{
    var str = '';
    for (var i = 0; i < byteArray.length; i++)
    {
        str +=  byteArray[i] <= 0x7F?
                byteArray[i] === 0x25 ? "%25" : // %
                String.fromCharCode(byteArray[i]) :
                "%" + byteArray[i].toString(16).toUpperCase();
    }
    return decodeURIComponent(str);
}

function fromByteArray(byteArray)
{
    var str = '';
    for (i = 0; i < byteArray.length; i++)
    {
        if (byteArray[i] <= 0x7F)
        {
            str += String.fromCharCode(byteArray[i]);
        }
        else
        {
            // Have to decode manually
            var ch = 0;
            var mask = 0x20;
            var j = 0;
            for (var mask = 0x20; mask != 0; mask >>=1 )
            {        
                var next = byteArray[j+1];
                if (next == undefined)
                {
                    abort("Unicode break in fromByteArray. The input is garbage");
                }
                ch = (ch << 6) ^ (next & 0x3f);
                if ((byteArray[i] & mask) == 0)
                    break;
                j++;
            }
            ch ^= (b & (0xff >> (i+3))) << (6*(i+1));
            str += String.fromCharCode(ch);
        }
    }
    return str;
}

function atom_to_memory_file(atom, memfile)
{
    var index = memory_files.length;
    memory_files[index] = {data:toByteArray(atable[VAL(atom)]),
                           ptr:0};
    var ftor = lookup_functor('$memory_file', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(memfile, ref);
}

function memory_file_to_atom(memfile, atom)
{
    if (TAG(memfile) != TAG_STR)
        return type_error("memory_file", memfile);
    ftor = VAL(memory[VAL(memfile)]);
    if (atable[ftable[ftor][0]] == "$memory_file" && ftable[ftor][1] == 1)
    {
        f = memory_files[VAL(memory[VAL(memfile)+1])];        
        return unify(atom, lookup_atom(fromByteArray(f.data)));
    }
    return type_error("memory_file", memfile);
}

function new_memory_file(memfile)
{
    var index = memory_files.length;
    memory_files[index] = {data:[],
                           ptr:0};
    var ftor = lookup_functor('$memory_file', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(memfile, ref);
}

function close_memory_file(stream)
{
    return true;
}

function read_memory_file(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    var memfile = memory_files[stream.data];
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = memfile.data[memfile.ptr++];            
            if (t === undefined)
                return records_read;
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

function write_memory_file(stream, size, count, buffer)
{
    var bytes_written = 0;
    var records_written;
    var memfile = memory_files[stream.data];
    for (records_written = 0; records_written < count; records_written++)
    {
        for (var b = 0; b < size; b++)
        {
            memfile.data[memfile.ptr++] = buffer[bytes_written++];
        }
    }
    return records_written;
}

function tell_memory_file(stream)
{
    return memory_files[stream.data].ptr;
}


function open_memory_file(memfile, mode, stream)
{
    var index = streams.length;
    if (TAG(memfile) == TAG_REF)
        return instantiation_error(memfile);
    if (TAG(memfile) != TAG_STR || memory[VAL(memfile)] != lookup_functor("$memory_file", 1))
        return type_error("memory_file", memfile);
    var memindex = get_arg(memfile, 1);
    if (TAG(memindex) != TAG_INT)
        return type_error("memory_file", memfile);
    memindex = VAL(memindex);
    if (TAG(mode) == TAG_REF)
        return instantiation_error(mode);
    else if (TAG(mode) != TAG_ATM)
        return type_error("atom", mode);
    if (atable[VAL(mode)] == 'read')
    {
        streams[index] = new_stream(read_memory_file, null, null, close_memory_file, tell_memory_file, memindex);
        
    }
    else if (atable[VAL(mode)] == 'write')
    {
        streams[index] = new_stream(null, write_memory_file, null, close_memory_file, tell_memory_file, memindex);
    }
    else
        return type_error("io_mode", mode);
    var ftor = lookup_functor('$stream', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(stream, ref);   
}

function free_memory_file(memfile)
{
    var m = memory_files[VAL(get_arg(memfile, 1))];
    memory_files[m] = null;
    return true;
}

function emit_code(address, c)
{
    // Not checking. Lets assume we know what we are doing!
    compile_buffer[VAL(address)] = VAL(c);
    return true;
}

function predicate_lookup_atom(atom, index)
{
    return unify(VAL(atom) ^ (TAG_INT << WORD_BITS), index);
}

function predicate_lookup_float(f, index)
{
    return unify(VAL(f) ^ (TAG_INT << WORD_BITS), index);
}

function predicate_lookup_functor(fname, arity, index)
{
    if (atable[VAL(fname)] === undefined)
        abort("Atom out of range: " + hex(deref(fname)));
    var i;
    for (i = 0; i < ftable.length; i++)
    {
        if (ftable[i][0] == VAL(fname) && ftable[i][1] == VAL(arity))
        {
            return unify(index, i ^ (TAG_INT << WORD_BITS));            
        }
    }
    i = ftable.length;
    ftable[i] = [VAL(fname), VAL(arity)];
    return unify(index, i ^ (TAG_INT << WORD_BITS));
}


function predicate_trace_unify(a, b)
{
    stdout("tracing unification of " + hex(a) + " and " + hex(b) + "\n");
    stdout("before, LHS = " + term_to_string(a) + "\n");
    stdout("before, RHS = " + term_to_string(b) + "\n");
    if (unify(a,b))
    {
        stdout("after, LHS = " + term_to_string(a) + "\n");
        stdout("after, RHS = " + term_to_string(b) + "\n");
        return true;
    }
    stdout("Failed to unify\n");
    return false;
}

function predicate_op(precedence, fixity, name)
{
    var names
    if (TAG(fixity) == TAG_REF)
        return instantiation_error(fixity);
    if (TAG(precedence) == TAG_REF)
        return instantiation_error(precedence);
    if (TAG(precedence) != TAG_INT)
        return type_error("integer", precedence);

    var op_precedence = VAL(precedence);
    var fixity = atable[VAL(fixity)];
    if (op_precedence < 0 || op_precedence > 1200)
        return domain_error("operator_priority", precedence);

    if (TAG(name) == TAG_ATM)
    {
        var n = atable[VAL(name)];
        if (n == ",")
            return permission_error("modify", "operator", name);
        else if (op_name == "|" && op_precedence < 1001)
            return permission_error("modify", "operator", name);
        names = [n];
    }
    else if (TAG(name) == TAG_LST)
    {
        names = [];
        var head = name;
        while (TAG(head) == TAG_LST)
        {
            if (TAG(deref(memory[VAL(head)])) == TAG_ATM)
            {
                var n = atable[deref(memory[VAL(head)])];
                if (n == ",")
                    return permission_error("modify", "operator", name);
                else if (op_name == "|" && op_precedence < 1001)
                    return permission_error("modify", "operator", name);                
                names.push(n);
            }
            else
                return type_error("atom", head);                
        }
        if (head != NIL)
        {
            if (TAG(head) == TAG_REF)
                return instantiation_error(head);
            else
                return type_error("atom", head);
        }
    }
    else
        return type_error("list", name);

    for (var i = 0; i < names.length; i++)
    {
        var op_name = names[i];

        if (fixity == "fx" || fixity == "fy")
        {
            if (op_precedence == 0)
                prefix_operators[op_name] = undefined;
            else
                prefix_operators[op_name] = {precedence: op_precedence, fixity:fixity};
        }
        else
        {
            if (op_precedence == 0)
                infix_operators[op_name] = undefined;
            else
                infix_operators[op_name] = {precedence: op_precedence, fixity:fixity};
        }
    } while (TAG(name) == TAG_LST);

    return true;
}

var gensyms = {};

function predicate_gensym(root, sym)
{
    if (gensyms[root] === undefined)
        gensyms[root] = 0;
    return unify(lookup_atom(atable[VAL(root)] + gensyms[root]), sym);
}

function prepend_clause_to_predicate(predicate, head, body)
{
    var predicate = VAL(lookup_functor(atable[VAL(deref(memory[VAL(predicate)+1]))], VAL(deref(memory[VAL(predicate)+2]))));
    if (predicates[predicate] === undefined)
    {
        // Easy case. New predicate. Add it to the table then set up the <NOP,0> header
        compile_buffer[0] = 254;
        compile_buffer[1] = 0;
        predicates[predicate] = {clauses: {0:{code:compile_buffer.slice(0), 
                                              key:0, 
                                              head:record_term(head), 
                                              body:record_term(body)}},
                                 clause_keys: [0],
                                 key:predicate,
                                 is_public: true,
                                 next_key: 1};
    }
    else
    {
        var first_key = predicates[predicate].clause_keys[0];
        var first_clause = predicates[predicate].clauses[first_key];
        if (first_clause.code[0] == 254)
        {
            // First clause was NOP - ie only clause. Make it trust_me, and the new clause is try_me_else
            compile_buffer[0] = 28;
            compile_buffer[1] = first_key;
            first_clause.code[0] = 30;
            first_clause.code[1] = 0;
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.unshift(predicates[predicate].next_key);
            predicates[predicate].next_key++;
            
        }
        else if (first_clause.code[0] == 28)
        {
            // first clause was try_me_else. It becomes retry_me_else
            // Our new clause is try_me_else
            compile_buffer[0] = 28;
            compile_buffer[1] = first_key;
            first_clause.code[0] = 29;
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.unshift(predicates[predicate].next_key);
            predicates[predicate].next_key++;            
        }
        else
            abort("Garbage clauses in prepend: " + first_clause.code[0]);
    }
    return true;
}

function check_compile_buffer(head, body)
{
    // Paranoia
    for (var z = 0; z < compile_buffer.length; z++)
    {
        if (compile_buffer[z] == null)
        {
            debug(term_to_string(head) + ":- " + term_to_string(body));
            debug(JSON.stringify(compile_buffer));
            abort("Illegal compile buffer: Address " + z + " is null!");
        }
    }
}
function add_clause_to_predicate(predicate, head, body)
{
    var predicate = VAL(lookup_functor(atable[VAL(deref(memory[VAL(predicate)+1]))], VAL(deref(memory[VAL(predicate)+2]))));
    if (predicates[predicate] === undefined)
    {
        // Easy case. New predicate. Add it to the table then set up the <NOP,0> header
        compile_buffer[0] = 254;
        compile_buffer[1] = 0;
        check_compile_buffer(head, body);
        predicates[predicate] = {clauses: {0:{code:compile_buffer.slice(0), 
                                              key:0, 
                                              head:record_term(head), 
                                              body:record_term(body)}},
                                 key:predicate,
                                 clause_keys: [0],
                                 is_public: true,
                                 next_key: 1};
    }
    else
    {
        var last_key = predicates[predicate].clause_keys[predicates[predicate].clause_keys.length-1];
        var last_clause = predicates[predicate].clauses[last_key];
        if (last_clause.code[0] == 254)
        {
            // Last clause was NOP - ie only clause. Make it try_me_else, and the new clause is trust_me
            last_clause.code[0] = 28;
            last_clause.code[1] = predicates[predicate].next_key;
            compile_buffer[0] = 30;
            compile_buffer[1] = 0;
            check_compile_buffer(head, body);            
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.push(predicates[predicate].next_key);
            predicates[predicate].next_key++;
            
        }
        else if (last_clause.code[0] == 30)
        {
            // last clause was trust_me, so there is already a try_me_else. Make it retry_me_else and add new clause as trust_me
            last_clause.code[0] = 29;
            last_clause.code[1] = predicates[predicate].next_key;
            compile_buffer[0] = 30;
            compile_buffer[1] = 0;
            //compile_buffer.unshift(predicates[predicate].next_key); WHAT?
            check_compile_buffer(head, body);            
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.push(predicates[predicate].next_key);
            predicates[predicate].next_key++;            
        }
        else
            abort("Garbage clauses: " + last_clause.code[0]);
    }

    return true;
}

function add_clause_to_aux(label, n, l, lt)
{
    if (TAG(label) == TAG_STR && memory[VAL(label)] == lookup_functor("defined", 1))
    {
        add_clause_to_existing(VAL(memory[VAL(label)+1]), VAL(n) ^ 0x80000000);
        unify(l, lt);
    }
    else
    {
        compile_buffer[VAL(n)] = 254;
        compile_buffer[VAL(n)+1] = 0;
        var ptr = state.H;
        memory[state.H++] = lookup_functor("defined", 1);
        memory[state.H++] = n;
        unify(label, ptr ^ (TAG_STR << WORD_BITS));

        var ptr2 = state.H;
        var ftor = lookup_functor("label", 2);
        memory[state.H++] = ftor;
        memory[state.H++] = label;
        memory[state.H++] = n;

        var ptr3 = state.H; // should unify with l
        memory[state.H++] = (ptr2) ^ (TAG_STR << WORD_BITS);

        var ptr4 = state.H;
        alloc_var();
        unify(ptr4, lt);

        unify(l, ptr3 ^ (TAG_LST << WORD_BITS));
    }
    return true;
}

function add_clause_to_existing(address, offset)
{
    while(true)
    {
        switch(compile_buffer[address])
        {
        case 254:
            // Change <NOP,0> -> try_me_else offset
            compile_buffer[address] = 28;
            compile_buffer[address+1] = offset;
            // Add <trust_me,0> for new clause
            compile_buffer[offset ^ 0x80000000] = 30;
            compile_buffer[(offset ^ 0x80000000)+1] = 0;
            return;
        case 30:
            // Change <trust_me,0> -> <retry_me_else, N>
            compile_buffer[address] = 29
            compile_buffer[address+1] = offset;
            // Add <trust_me,0> for new clause
            compile_buffer[offset ^ 0x80000000] = 30;
            compile_buffer[(offset ^ 0x80000000)+1] = 0;
            return;
        case 28:
        case 29:
            address = compile_buffer[address+1] ^ 0x80000000;
            break;
        default:
            abort("Garbage in code array: " + compile_buffer[address]);
        }        
    }
}


function create_choicepoint()
{
    // Create a choicepoint
    if (state.E > state.B)
    {
        newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
    } 
    else
    {
        newB = state.B + memory[state.B] + 8;
    }
    memory[newB] = state.num_of_args+2;
    var n = memory[newB];
    memory[newB + 1] = 0;
    memory[newB + 2] = {code: code,
                        offset: state.P};
    for (i = 0; i < state.num_of_args; i++)
    {
        memory[newB + 3 + i] = register[i];
    }
    // Save the current context
    memory[newB+n+1] = state.E;
    memory[newB+n+2] = state.CP;
    memory[newB+n+3] = state.B;
//    memory[newB+n+4] = retry_foreign;
    memory[newB+n+4] = {code: bootstrap_code,                        
                        predicate:state.current_predicate,  // Suspect
                        offset:retry_foreign_offset};
    memory[newB+n+5] = state.TR;
    memory[newB+n+6] = state.H;
    memory[newB+n+7] = state.B0;
    state.B = newB;
    state.HB = state.H;
    return true;
}

function update_choicepoint_data(value)
{
    memory[state.B+1] = value;
    return true;
}


function destroy_choicepoint()
{
    n = memory[state.B];
    unwind_trail(memory[state.B + n + 5], state.TR);
    state.B = memory[state.B + n + 3];
    state.HB = memory[state.B+ memory[state.B] + 6];
}

// For testing only! Assumes -,+ mode
function member(element, list)
{
    if (state.foreign_retry)
    {
        list = state.foreign_value;
    }
    else
    {
        create_choicepoint();
    }    
    while(TAG(list) == TAG_LST)
    {
        head = memory[VAL(list)];
        if (unify(head, element))
        {
            update_choicepoint_data(memory[VAL(list)+1]);
            return true;
        }
        list = memory[VAL(list)+1]
    }
    destroy_choicepoint();
    return false;
}



function predicate_debug()
{
    debugging = true;
    return true;
}

function predicate_nodebug()
{
    debugging = false;
    return true;
}

function predicate_jmp(vars)
{
    state.P = -1; // PC will be incremented by 3 after this if we succeed to 2. This is where queries are compiled from, since the first two bytes are for try/retry/trust
    code = compile_buffer.slice(0);
    register[0] = vars;
    return true;
}

function mark_top_choicepoint(vars_list, markpoint)
{
    var vars = [];
    while(TAG(vars_list) == TAG_LST)
    {        
        vars.push(memory[VAL(vars_list)]);        
        vars_list = memory[VAL(vars_list) + 1];
    }
    if (vars_list != NIL)
        abort("Invalid list in mark_top_choicepoint");

    mark = {B: state.B,
            V: vars,
            P: state.P+3,
            code: code};
    cleanups.unshift(mark);
    // Skip the cleanup code
    state.P += 4;
    return unify(markpoint, state.B ^ (TAG_INT << WORD_BITS));
}

// FIXME: Not implemented: [c, d, D, e, E, I, N, p, s, @, t, |, +]
function predicate_format(stream, fmt, args)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    stream = s.value;
    result = "";
    fmt = atable[VAL(fmt)];
    var arg = args;
    var numarg = undefined;
    for (i = 0; i < fmt.length; i++)
    {
        c = fmt.charAt(i);
        if (c == '~')
        {
            while (true)
            {
                switch (fmt.charAt(i+1))
                {
                case 'a':
                    if (TAG(memory[VAL(arg)]) != TAG_ATM)
                        return type_error("atom", arg);
                    // fall-through
                case 'w':
                    result += format_term(memory[VAL(arg)], {ignore_ops:false, numbervars:true, quoted:false});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'W':
                    var a = memory[VAL(arg)];
                    arg = memory[VAL(arg)+1];
                    var options = parse_term_options(memory[VAL(arg)]);
                    result += format_term(a, options);
                    arg = memory[VAL(arg)+1];
                    break;
                    
                case 'i':
                    arg = memory[VAL(arg)+1];
                    break;
                case 'q':
                    result += format_term(memory[VAL(arg)], {ignore_ops:false, numbervars:true, quoted:true});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'k':
                    result += format_term(memory[VAL(arg)], {ignore_ops:true, numbervars:true, quoted:true});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'n':
                    result += "\n";
                    break;
                case '~':
                    result += "~";
                    break;
                case 'r':
                case 'R':
                    if (numarg == undefined)
                        return format_error("r,R requires radix specifier");
                    var e = {};
                    if (!evaluate_expression(memory[VAL(arg)], e))
                        return false;
                    if (fmt.charAt(i+1) == 'R')
                        result += e.value.toString(numarg).toUpperCase();
                    else
                        result += e.value.toString(numarg);
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                    numarg = fmt.charAt(i+1) - '0';
                    i+=2;
                    while (fmt.charAt(i) >= '0' && fmt.charAt(i) <= '9')
                    {
                        numarg = (numarg * 10) + (fmt.charAt(i)-'0');
                        i++;
                    }
                    i--;
                    continue;                
                default:
                    return existence_error("format_character", lookup_atom(fmt.charAt(i+1)));
                }
                i++;
                break; // Really this is just a goto for the numarg reading
            }
        }
        else if (c == '\\')
        {
            switch(fmt.charAt(i+1))
            {
            case '\\':
                result += "\\";
                break;
            case "n":
                result += "\n";
                break;
            default:
                abort("Unimplemented or escape character: " + fmt.charAt(i+1));
            }
            i++;
        }
        else
            result += c;
    }
    var bytes = toByteArray(result);
    return (stream.write(stream, 1, bytes.length, bytes) >= 0)
}

function unmark_choicepoint(mark)
{
    mark = VAL(mark);    
    for (var i = 0; i < cleanups.length; i++)
    {
        if (cleanups[i].B == mark)
        {
            cleanups.splice(i, 1);
            // Additionally, we have to actually cut this choicepoint as well. This deserves an explanation!
            // Suppose we nest setup_call_cleanup(true, setup_call_cleanup(true, true, true), true).
            // Once we complete the inner true, we will unmark the choicepoint that allows us to distinguish exit from _.
            // but unless we cut the parent choicepoint (which allows us to distinguish success from error/failure)
            // this will persist. The outer cleanup will then see a choicepoint, even though the inner one has succeeded 
            // deterministically, and will exit with unbound port.
            state.B = memory[mark + memory[mark]+3];
            if (state.B > 0)
                tidy_trail();
            return true;
        }
    }
    debug("Looking for " + mark);
    debug(JSON.stringify(cleanups));
    abort("nope");
}

// This is used in the failure port. Since we have failed into the failure branch of the cleanup, there cannot be any choicepoints around except for the 
// one that got us here. Therefore, we can just delete the first cleanup handler (I hope!)
function unmark_top_choicepoint()
{
    cleanups.shift();
    return true;
}

function predicate_copy_term(t1, t2)
{
    return unify(t2, recall_term(record_term(t1), {}));
}


function predicate_repeat()
{
    // Create a choicepoint that points to itself
    if (state.E > state.B)
    {
        newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
    } 
    else
    {
        newB = state.B + memory[state.B] + 8;
    }
    memory[newB] = state.num_of_args+2;
    var n = memory[newB];
    memory[newB + 1] = 0;
    memory[newB + 2] = {code: code,
                        offset: state.P};
    for (i = 0; i < state.num_of_args; i++)
    {
        memory[newB + 3 + i] = register[i];
    }
    // Save the current context
    memory[newB+n+1] = state.E;
    memory[newB+n+2] = state.CP;
    memory[newB+n+3] = state.B;
    memory[newB+n+4] = {code: code,
                        predicate: state.current_predicate, // suspect!
                        offset: state.P}; // Retry will just create the choicepoint again!
    memory[newB+n+5] = state.TR;
    memory[newB+n+6] = state.H;
    memory[newB+n+7] = state.B0;
    state.B = newB;
    state.HB = state.H;
    return true;
}

var flags = [];

function predicate_flag(key, old_value, new_value)
{
    if (TAG(key) == TAG_REF)
        return instantiation_error(key);
    if (TAG(key) != TAG_ATM)
        return type_error("atom", key);
    key = atable[VAL(key)];
    var o = (TAG_INT << WORD_BITS);
    if (flags[key] !== undefined)
        o = flags[key] ^ (TAG_INT << WORD_BITS)
    if (!unify(o, old_value))
        return false;
    var n = {};
    if (evaluate_expression(new_value, n))
        flags[key] = n.value;
    else 
        return false;
    return true;
}

function predicate_atom_length(atom, length)
{
    if (TAG(atom) == TAG_REF)
        return instantiation_error(atom);
    if (TAG(atom) != TAG_ATM)
        return type_error("atom", atom);
    return unify(atable[VAL(atom)].length ^ (TAG_INT << WORD_BITS), length);    
}

function predicate_atom_concat(atom1, atom2, atom12)
{
    var index;
    if (!state.foreign_retry)
    {        
        // First call, or deterministic
        if (TAG(atom1) == TAG_REF && TAG(atom12) == TAG_REF)
            return instantiation_error(atom1);
        if (TAG(atom1) != TAG_REF && TAG(atom1) != TAG_ATM)
            return type_error("atom", atom1);
        if (TAG(atom2) != TAG_REF && TAG(atom2) != TAG_ATM)
            return type_error("atom", atom2);
        if (TAG(atom12) != TAG_REF && TAG(atom12) != TAG_ATM)
            return type_error("atom", atom12);
        if (TAG(atom1) == TAG_ATM && TAG(atom2) == TAG_ATM)
        {
            // Deterministic case
            return unify(atom12, lookup_atom(atable[VAL(atom1)] + atable[VAL(atom2)]));
        }
        else 
        {
            // Nondeterministic case. Need a choicepoint:
            create_choicepoint();
            index = 0;
        }
    }
    else
    {
        index = state.foreign_value+1;
    }
    update_choicepoint_data(index);
    // Drop through to general nondeterministic case
    if (index == atable[VAL(atom12)].length+1)
    {
        destroy_choicepoint();
        return false;
    }
    if (unify(atom1, lookup_atom(atable[VAL(atom12)].substring(0, index))) && unify(atom2, lookup_atom(atable[VAL(atom12)].substring(index))))
        return true;
    return false;
}

function predicate_char_code(atom, code)
{
    if (TAG(atom) == TAG_REF && TAG(code) == TAG_REF)
        return instantiation_error(atom);
    if (TAG(atom) == TAG_ATOM)
    {
        a = atable[VAL(atom)];
        if (a.length != 1)
            return type_error("character", atom);
        return unify(code, a.charCodeAt(0) ^ (TAG_INT << WORD_BITS));
    }
    else if (TAG(code) == TAG_INT)
    {
        if (VAL(code) < 0)
            return representation_error("character_code", code);
        return unify(atom, lookup_atom(String.fromCharCode(VAL(code))));
    }
}

function predicate_atom_chars(atom, chars)
{
    if (TAG(chars) == TAG_REF)
    {
        // Atom -> chars
        if (TAG(atom) != TAG_ATM)
            return type_error("atom", atom);
        var a = atable[VAL(atom)].split('');
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = lookup_atom(a[i]);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(chars, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Chars -> Atom
        var a = [];
        while (TAG(chars) == TAG_LST)
        {
            a.push(atable[VAL(memory[VAL(chars)])]);
            chars = memory[VAL(chars)+1];
        }
        if (chars != NIL)
            return type_error("list", chars);
        return unify(atom, lookup_atom(a.join('')));            
    }
}

function predicate_atom_codes(atom, codes)
{
    if (TAG(codes) == TAG_REF)
    {
        // Atom -> codes
        if (TAG(atom) != TAG_ATM)
            return type_error("atom", atom);
        var a = atable[VAL(atom)];
        var tmp = state.H ^ (TAG_LST << WORD_BITS);
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = a.charCodeAt(i) ^ (TAG_INT << WORD_BITS);
            // If there are no more items we will overwrite the last entry with [] when we exit the loop
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(codes, tmp);
    }
    else
    {
        // Codes -> Atom
        var a = [];
        while (TAG(codes) == TAG_LST)
        {
            a.push(String.fromCharCode(memory[VAL(codes)]));
            codes = memory[VAL(codes)+1];
        }
        if (codes != NIL)
            return type_error("list", codes);
        return unify(atom, lookup_atom(a.join('')));            
    }
}
// return -1 if a < b
// return 0 if a == b
// return 1 if a > b
//
function compare_terms(a, b)
{
    switch(TAG(a))
    {
    case TAG_REF:
        if (TAG(b) == TAG_REF)
        {
            if (a == b)
                return 0;
            else if (a > b)
                return 1;
        }
        return -1;
    case TAG_FLT:
        if (TAG(b) == TAG_REF)
            return 1;
        if (TAG(b) == TAG_FLT)
        {
            if (floats[VAL(a)] == floats[VAL(b)])
                return 0;
            else if (floats[VAL(a)] > floats[VAL(b)])
                return 1;
        }
        return -1;
    case TAG_INT:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT)
            return 1;
        if (TAG(b) == TAG_INT)
        {
            if (VAL(a) == VAL(b))
                return 0;
            else if (VAL(a) > VAL(b))
                return 1;
        }
        return -1;
    case TAG_ATM:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT || TAG(b) == TAG_INT)
            return 1;
        if (TAG(b) == TAG_ATM)
        {
            if (atable[VAL(a)] == atable[VAL(b)])
                return 0;
            else if (atable[VAL(a)] > atable[VAL(b)])
                return 1;
        }
        return -1;
    case TAG_STR:
    case TAG_LST:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT || TAG(b) == TAG_INT || TAG(b) == TAG_ATM)
            return 1;
        var aftor;
        var bftor;
        if (TAG(a) == TAG_LST)
            aftor = lookup_functor(".", 2);
        else
            aftor = memory[VAL(a)];
        if (TAG(b) == TAG_LST)
            bftor = lookup_functor(".", 2);
        else
            bftor = memory[VAL(b)];
        if (ftable[VAL(aftor)][1] > ftable[VAL(bftor)][1])
            return 1;
        else if (ftable[VAL(aftor)][1] < ftable[VAL(bftor)][1])
            return -1;
        // At this point the arity is equal and we must compare the functor names
        if (atable[ftable[VAL(aftor)][0]] > atable[ftable[VAL(bftor)][0]])
            return 1;
        else (atable[ftable[VAL(aftor)][0]] < atable[ftable[VAL(bftor)][0]])
            return -1;
        // So the functors are the same and we must compare the arguments.
        for (i = 0; i < ftable[VAL(aftor)][1]; i++)
        {
            var result = compare_terms(memory[VAL(a)+1+i], memory[VAL(b)+1+i]);
            if (result != 0)
                return result;
        }
    }
    return 0;
}

function predicate_compare(x, a, b)
{
    var i = compare_terms(a,b);
    if (i > 0) 
        return unify(x, lookup_atom(">"));
    else if (i < 0) 
        return unify(x, lookup_atom("<"));
    else
        return unify(x, lookup_atom("="));
}

function predicate_term_lt(a, b)
{
    return compare_terms(a,b) == -1;
}

function predicate_term_elt(a, b)
{
    return compare_terms(a,b) != 1;
}

function predicate_term_gt(a, b)
{
    return compare_terms(a,b) == 1;
}

function predicate_term_egt(a, b)
{
    return compare_terms(a,b) != -1;
}


function predicate_acyclic_term(t)
{
    var visited_cells = [];
    var stack = [t];
    while (stack.length != 0)
    {        
        var arg = stack.pop();
        switch (TAG(arg))
        {
        case TAG_INT:
        case TAG_FLT:
        case TAG_ATM:
            continue;
        case TAG_REF:
            var needle = deref(arg);
            for (var i = 0; i < visited_cells.length; i++)
            {
                if (visited_cells[i] == needle)
                {
                    return false;
                }
            }
            continue;
        case TAG_LST:
            visited_cells.push(arg);
            stack.push(memory[VAL(arg)]);
            stack.push(memory[VAL(arg)+1]);
            continue;
        case TAG_STR:
            visited_cells.push(arg);
            var arity = ftable[VAL(memory[VAL(arg)])][1];
            for (var i = 0; i < arity; i++)
                stack.push(memory[VAL(arg)+1+i]);
            continue;
        }
    }
    return true;
}

function predicate_number_chars(n, chars)
{
    if (TAG(chars) == TAG_REF)
    {
        // Atom -> chars
        var a;
        if (TAG(n) == TAG_INT)
            a = (VAL(n) + "").split('');
        else if (TAG(n) == TAG_FLT)
            a = (floats[VAL(n)] + "").split('');
        else
            return type_error("number", n);
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = lookup_atom(a[i]);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(chars, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Chars -> Atom
        var a = [];
        while (TAG(chars) == TAG_LST)
        {
            a.push(atable[VAL(memory[VAL(chars)])]);
            chars = memory[VAL(chars)+1];
        }
        if (chars != NIL)
            return type_error("list", chars);
        var f = parseFloat(a.join(''));
        // FIXME: Overflows
        if (~~f == f)
            return unify(n, f ^ (TAG_INT << WORD_BITS));
        else
        {            
            return unify(n, lookup_float(f));
        }
    }
}

function lookup_float(f)
{
    for (var i = 0; i < floats.length+1; i++)
    {
        if (floats[i] == f)
        {
            return i ^ (TAG_FLT << WORD_BITS);
        }
        if (floats[i] === undefined)
        {
            floats[i] = f;
            return i ^ (TAG_FLT << WORD_BITS);
        }
    }
    abort("Should not get here");
}

function predicate_number_codes(n, codes)
{
    if (TAG(codes) == TAG_REF)
    {
        // Atom -> codes
        var a;
        if (TAG(n) == TAG_INT)
        {
            a = VAL(n) + "";
        }
        else if (TAG(n) == TAG_FLT)
        {
            a = floats[VAL(n)] + "";
        }
        else
            return type_error("number", n);
        var a = (VAL(n) + "");
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = a.charCodeAt(i) ^ (TAG_INT << WORD_BITS);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(codes, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Codes -> Atom
        var a = [];
        while (TAG(codes) == TAG_LST)
        {
            a.push(String.fromCharCode(memory[VAL(codes)]));
            codes = memory[VAL(codes)+1];
        }
        if (codes != NIL)
            return type_error("list", codes);
        var f = parseFloat(a.join(''));
        // FIXME: Overflows
        if (~~f == f)
            return unify(n, f ^ (TAG_INT << WORD_BITS));
        else
            return unify(n, lookup_float(f));
    }
}

function predicate_subsumes_term(a, b)
{
    var before = term_variables(b);
    create_choicepoint();
    if (!unify(a,b))
    {
        destroy_choicepoint();
        return false;
    }
    if (!predicate_acyclic_term(b))
    {
        destroy_choicepoint();
        return false;
    }
    var after = term_variables(b);
    // We need to save a bit of info for this backtrack to not cause us some serious problems
    var oldP = state.P;
    var oldcode = code;
    var oldPred = state.current_predicate;
    backtrack();
    state.P = oldP;
    code = oldcode;
    state.current_predicate = oldPred;

    destroy_choicepoint();
    return (after.length == before.length);
}


function predicate_current_op(precedence, fixity, name)
{
    if (state.foreign_retry)
    {
        index = state.foreign_value + 1;         
    }
    else
    {
        create_choicepoint();
        index = 0;
    }
    update_choicepoint_data(index);
    // This is horrific
    var infix_count = Object.keys(infix_operators).length;
    var prefix_count = Object.keys(prefix_operators).length;
    if (index >= infix_count + prefix_count)
    {
        destroy_choicepoint();
        return false;
    }
    else if (index >= infix_count)
    {
        try_name = Object.keys(prefix_operators)[index - infix_count];
        try_fixity = prefix_operators[try_name].fixity;
        try_precedence = prefix_operators[try_name].precedence;
    }
    else
    {
        try_name = Object.keys(infix_operators)[index];
        try_fixity = infix_operators[try_name].fixity;
        try_precedence = infix_operators[try_name].precedence;
    }
    return unify(name, lookup_atom(try_name)) && unify(fixity, lookup_atom(try_fixity)) && unify(precedence, try_precedence ^ (TAG_INT<<WORD_BITS));
}

var prolog_flags = [{name:"bounded", fn:flag_bounded},
                    {name:"max_integer", fn:flag_max_integer},
                    {name:"min_integer", fn:flag_min_integer},
                    {name:"integer_rounding_function", fn:flag_integer_rounding_function},
                    {name:"char_conversion", fn:flag_char_conversion},
                    {name:"debug", fn:flag_debug},
                    {name:"max_arity", fn:flag_max_arity},
                    {name:"unknown", fn:flag_unknown},
                    {name:"double_quotes", fn:flag_double_quotes}];

var prolog_flag_values = {char_conversion: false,
                          debug: false,
                          unknown: "error",
                          double_quotes: "codes"};

function flag_bounded(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("true"));
}

function flag_max_integer(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, (268435455) ^ (TAG_INT<<WORD_BITS));
}

function flag_min_integer(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, (536870911) ^ (TAG_INT<<WORD_BITS));
}

function flag_integer_rounding_function(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("toward_zero"));
}

function flag_char_conversion(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "on")
            prolog_flag_values.char_conversion = true;
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "off")
            prolog_flag_values.char_conversion = false;
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, prolog_flag_values.char_conversion?lookup_atom("on"):lookup_atom("off"));
}

function flag_debug(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "on")
            prolog_flag_values.debug = true;
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "off")
            prolog_flag_values.debug = false;
        else
        {
            return type_error("flag_value", value);
        }
        return true;
    }
    return unify(value, prolog_flag_values.debug?lookup_atom("on"):lookup_atom("off"));
}

function flag_max_arity(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("unbounded"));
}

function flag_unknown(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "error")
            prolog_flag_values.unknown = "error";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "fail")
            prolog_flag_values.unknown = "fail";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "warning")
            prolog_flag_values.unknown = "warning";
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, lookup_atom(prolog_flag_values.unknown));
}

function flag_double_quotes(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "chars")
            prolog_flag_values.double_quotes = "chars";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "codes")
            prolog_flag_values.double_quotes = "codes";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "atom")
            prolog_flag_values.double_quotes = "atom";
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, lookup_atom(prolog_flag_values.double_quotes));
}

function predicate_set_prolog_flag(key, value)
{
    if (TAG(key) != TAG_ATM)
        return type_error("atom", key);
    keyname = atable[VAL(key)];    
    
    for (var i = 0; i < prolog_flags.length; i++)
    {
        if (prolog_flags[i].name == keyname)
        {
            return prolog_flags[i].fn(true, value);
        }
    }
    debug("No such flag");
    return false;
}

function predicate_current_prolog_flag(key, value)
{
    if (TAG(key) == TAG_REF)
    {
        if (state.foreign_retry)
        {
            index = state.foreign_value + 1;         
        }
        else
        {
            create_choicepoint();
            index = 0;
        }
        update_choicepoint_data(index);        
        if (index >= prolog_flags.length)
        {
            destroy_choicepoint();
            return false;
        }
        unify(key, lookup_atom(prolog_flags[index].name));
        return prolog_flags[index].fn(false, value);        
    }
    else if (TAG(key) == TAG_ATM)
    {
        keyname = atable[VAL(key)];    
        var index = 0;
        for (var i = 0; i < prolog_flags.length; i++)
        {
            if (prolog_flags[index].name == keyname)
                return prolog_flags[index].fn(false, value);
        }
        return false;
    }
    else
        return type_error("atom", key);
}

function predicate_clause(head, body)
{
    var ftor;
    var index;
    if (TAG(head) == TAG_REF)
        return instantiation_error(head);
    else if (TAG(head) == TAG_ATM)
    {
        ftor = VAL(lookup_functor(atable[VAL(head)], 0));
    }
    else if (TAG(head) == TAG_STR)
    {
        ftor = VAL(memory[VAL(head)]);
    }
    else
        return type_error("callable", head);
    if (predicates[ftor].is_public != true)
        return permission_error("access", "private_procedure", head);
    if (!state.foreign_retry)
    {
        create_choicepoint();
        index = 0;
    }
    else
    {
        index = state.foreign_value + 1;
    }
    update_choicepoint_data(index);
    if (index >= predicates[ftor].clause_keys.length)
    {
        destroy_choicepoint();
        return false;
    }
    var key = predicates[ftor].clause_keys[index];
    var varmap = {};
    var head_ref = recall_term(predicates[ftor].clauses[key].head, varmap);
    if (unify(head_ref, head))
    {
        if (unify(recall_term(predicates[ftor].clauses[key].body, varmap), body))
        {
            return true;
        }
        return false;
            
    }
    else
    {
        return false;    
    }
}


function predicate_current_predicate(indicator)
{
    var slash2 = lookup_functor("/", 2);
    if (!state.foreign_retry)
    {
        if (TAG(indicator) == TAG_STR)
        {
            if (memory[VAL(indicator)] == slash2)
            {
                var name = memory[VAL(indicator) + 1];
                var arity = memory[VAL(indicator) + 2];
                if (TAG(arity) != TAG_INT && TAG(arity) != TAG_REF)
                    return type_error("integer", arity);
                if (TAG(name) != TAG_ATM && TAG(name) != TAG_REF)
                    return type_error("atom", name);
                
                if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
                {
                    // Deterministic
                    var ftor = VAL(lookup_functor(atable[VAL(name)], VAL(arity)));
                    if (predicates[ftor] !== undefined)
                        return true;
                    else if (foreign_predicates[ftor] !== undefined)
                        return true;
                    return false;
                }
            }
            else
                return type_error("predicate_indicator", indicator);
        }
        // We are going to have to enumerate all predicates
        create_choicepoint();
        index = 0;
    }
    else
        index = state.foreign_value + 1;
    // Horrific :(

    if (index >= Object.keys(predicates).length)
    {
        destroy_choicepoint();
        return false;
    }
    update_choicepoint_data(index);
    var key = Object.keys(predicates)[index];
    var result = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = slash2;
    memory[state.H++] = ftable[key][0] ^ (TAG_ATM << WORD_BITS);
    memory[state.H++] = ftable[key][1] ^ (TAG_INT << WORD_BITS);;
    return unify(result, indicator);
}

function predicate_abolish(indicator)
{
    var slash2 = lookup_functor("/", 2);
    if (TAG(indicator) == TAG_STR && memory[VAL(indicator)] == slash2)
    {
        var name = deref(memory[VAL(indicator) + 1]);
        var arity = deref(memory[VAL(indicator) + 2]);
        if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
        {
            if (VAL(arity) < 0)
                return domain_error("not_less_than_zero", arity);
            var ftor = VAL(lookup_functor(atable[VAL(name)], VAL(arity)));
            if (predicates[ftor].is_public !== true)
                return permission_error("modify", "static_procedure", indicator);
            predicates[ftor] = undefined;
            return true;
        }
        else if (TAG(name) == TAG_REF)
            return instantiation_error(name);
        else if (TAG(name) != TAG_ATM)
            return type_error("atom", name);
        else if (TAG(arity) == TAG_REF)
            return instantiation_error(arity);
        else if (TAG(arity) != TAG_INT)
            return type_error("integer", arity);
    }
    else if (TAG(indicator) == TAG_REF)
        return instantiation_error(indicator);
    else
        return type_error("predicate_indicator", indicator);
}

function predicate_retract_clause(head, body)
{
    var ftor;
    var index;
    if (TAG(head) == TAG_REF)
        return instantiation_error(head);
    else if (TAG(head) == TAG_ATM)
    {
        ftor = VAL(lookup_functor(atable[VAL(head)], 0));
    }
    else if (TAG(head) == TAG_STR)
    {
        ftor = VAL(memory[VAL(head)]);
    }
    else
        return type_error("callable", head);
    if (predicates[ftor].is_public != true)
        return permission_error("access", "static_procedure", head);
    if (!state.foreign_retry)
    {
        create_choicepoint();
        index = 0;
    }
    else
    {
        index = state.foreign_value + 1;
    }
    update_choicepoint_data(index);
    if (index >= predicates[ftor].clause_keys.length)
    {
        destroy_choicepoint();
        return false;
    }
    var key = predicates[ftor].clause_keys[index];
    var varmap = {};
    var head_ref = recall_term(predicates[ftor].clauses[key].head, varmap);
    if (unify(head_ref, head))
    {
        var body_ref = recall_term(predicates[ftor].clauses[key].body, varmap);
        if (unify(body_ref, body))
        {
            // Delete this clause. This is not a trivial operation!
            var p = predicates[ftor];
            // First case: This is the only predicate
            if (p.clause_keys.length == 1)
            {
                predicates[ftor] = undefined;
                destroy_choicepoint();
                return true;
            }
            else if (index == 0)
            {
                // Delete the first clause. Update the second clause from either:
                // 1) trust_me -> NOP
                // 2) retry_me_else -> try_me_else
                if (p.clauses[p.clause_keys[1]].code[0] == 30)
                    p.clauses[p.clause_keys[1]].code[0] = 254;
                else if (p.clauses[p.clause_keys[1]].code[0] == 29)
                    p.clauses[p.clause_keys[1]].code[0] = 28;
                else
                    abort("Garbage clauses in retract: " + p.clauses[p.clause_keys[1]].code[0]);
                p.clauses[key] = undefined;
                // and remove the key
                p.clauses[key] = undefined;
                p.clause_keys.shift();
                update_choicepoint_data(index-1);
                return true;
            }
            else if (index == p.clause_keys.length-1)
            {
                // Remove the last clause. Update the second-to-last clause from either:
                // 1) try_me_else -> NOP
                // 2) retry_me_else -> trust_me
                if (p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] == 28)
                    p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] = 254;
                else if (p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] == 29)
                    p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] = 30;
                else
                    abort("Garbage clauses in retract: " + p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0]);            
                // and remove the key
                p.clauses[key] = undefined;
                p.clause_keys.pop();
                destroy_choicepoint();
                return true;
            }
            else
            {
                // Delete a clause from the middle. Update the previous clause from either:
                // try_me_else N -> try_me_else <following clause key>
                // retry_me_else N -> retry_me_else <following clause key>
                p.clauses[p.clause_keys[index-1]].code[1] = p.clause_keys[index+1];
                // and remove the key
                p.clauses[key] = undefined;
                for (var i = 0; i < p.clause_keys.length; i++)
                {
                    if (p.clause_keys[i] == key)
                    {
                        p.clause_keys.splice(i, 1);
                        update_choicepoint_data(index-1);
                        return true;
                    }
                }
                abort("No such key?!");
            }
        }
    }
    return false; // Nothing to retract
}

function predicate_sub_atom(source, start, length, remaining, subatom)
{
    var index;
    if (TAG(source) == TAG_REF)
        return instantiation_error(source);
    else if (TAG(source) != TAG_ATM)
        return type_error("atom", source);
    if (TAG(subatom) != TAG_ATM && TAG(subatom) != TAG_REF)
        return type_error("atom", subatom);
    var input = atable[VAL(source)];
    if (!state.foreign_retry)
    {
        index = {start:0, fixed_start:false, length:0, fixed_length:false, remaining:input.length, fixed_remaining:false};
        if (TAG(start) == TAG_INT)
        {
            index.fixed_start = true;
            index.start = VAL(start);
        }
        if (TAG(length) == TAG_INT)
        {
            index.fixed_length = true;
            index.length = VAL(length);
        }
        if (TAG(remaining) == TAG_INT)
        {
            index.fixed_remaining = true;
            index.remaining = VAL(remaining);
        }
        if (index.fixed_start && index.fixed_remaining && !index.fixed_length)
        {
            // Deterministic: Fall through to bottom case
            index.length = input.length-index.start-index.remaining;
            index.fixed_length = true;
        }
        if (index.fixed_remaining && index.fixed_length && !index.fixed_start)
        {
            // Deterministic: Fall through to bottom case
            index.start = input.length-index.length-index.remaining;
            index.fixed_start = true;
        }
        if (index.fixed_start && index.fixed_length)
        {
            // Deterministic general case.
            return unify(remaining, (input.length-index.start-index.length) ^ (TAG_INT << WORD_BITS)) && 
                unify(start, (index.start) ^ (TAG_INT << WORD_BITS)) && 
                unify(length, (index.length) ^ (TAG_INT << WORD_BITS)) && 
                unify(subatom, lookup_atom(input.substring(index.start, index.start+index.length)));
        }
        // Otherwise nondeterministic
        create_choicepoint();
    }
    else
    {
        index = state.foreign_value;
        if (!index.fixed_length)
        {
            index.length++;
            if (index.start + index.length > input.length)
            {
                index.length = 0;
                if (!index.fixed_start)
                {
                    index.start++;
                    if (index.start > input.length)
                    {
                        destroy_choicepoint();
                        return false;
                    }
                }
                else
                {
                    // start is fixed, so length and remaining are free
                    // but remaining is always just computed
                    destroy_choicepoint();
                    return false;
                }
            }
        }
        else
        {
            // length is fixed, so start and remaining must be free
            index.start++;
            index.remaining--;
            if (index.length + index.start > input.length)
            {
                destroy_choicepoint();
                return false;
            }
        }
    }
    update_choicepoint_data(index);
    return unify(remaining, (input.length-index.start-index.length) ^ (TAG_INT << WORD_BITS)) && 
        unify(start, (index.start) ^ (TAG_INT << WORD_BITS)) && 
        unify(length, (index.length) ^ (TAG_INT << WORD_BITS)) && 
        unify(subatom, lookup_atom(input.substring(index.start, index.start+index.length)));
}

/* errors */
function type_error(expected, got)
{
    var ftor = lookup_functor('type_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(expected);
    memory[state.H++] = got;
    return predicate_throw(ref);
}

function permission_error(action, type, instance)
{
    var ftor = lookup_functor('permission_error', 3);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(action);
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function instantiation_error(v)
{
    var ftor = lookup_functor('instantiation_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = v;
    return predicate_throw(ref);
}

function domain_error(domain, got)
{
    var ftor = lookup_functor('domain_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(domain);
    memory[state.H++] = got;
    return predicate_throw(ref);

}

function format_error(message)
{
    var ftor = lookup_functor('format_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}

function existence_error(type, instance)
{
    var ftor = lookup_functor('existence_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function representation_error(type, instance)
{
    var ftor = lookup_functor('representation_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function syntax_error(message)
{
    var ftor = lookup_functor('syntax_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}

function io_error(message)
{
    var ftor = lookup_functor('io_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}
// File wam.js
/* For general documentation, see wam_compiler.pl

Some helpful diagrams:
Environment frame looks like this:
              -----------
    state.E ->|0  | CE  |
              |1  | CP  |
              |2  | Y0  |
              |...|     |
              |n+1| Yn  |
              -----------

Choicepoint frame where we have tried something but can try 'Next' if it fails looks like this:
(There are n arguments, labelled from A0 to An-1)

              -------------
    state.B ->|0  | n     |
              |1  | A0    |
              |2  | A1    |
              |...|       |
              |n  | An-1  |
              |n+1| E     |
              |n+2| CP    |
              |n+3| B     |
              |n+4| Next  |
              |n+5| TR    |
              |n+6| H     |
              |n+7| B0    |
              -------------

*/



var ftable = [];
var atable = ['[]']; // Reserve first atom as [].
var floats = [];
var predicates = {};
var exception = null;

/* Constants. Should be auto-generated */
var HEAP_SIZE = 131070;
var STACK_SIZE = 65535;
var TRAIL_SIZE = 1000;
var READ = 0;
var WRITE = 1;
var TAG_REF = 0; // 0x00000000
var TAG_STR = 1; // 0x08000000
var TAG_LST = 2; // 0x10000000
var TAG_INT = 3; // 0x18000000
var TAG_ATM = 4; // 0x20000000
var TAG_FLT = 5; // 0x28000000
///////////// 6 is currently unused
var TAG_EXT = 7; // Reserved!
var TAG_MASK = 7;
// 3 bits are used for the tag
// 2 bits are used for GC
// This leaves 27 for the actual value, since javascript does not have 64-bit integers
var WORD_BITS = 27;
var M_BIT = 1 << 30;
var F_BIT = 1 << 31;
var NV_MASK = M_BIT | F_BIT | (TAG_MASK << WORD_BITS);

var NIL = (TAG_ATM << WORD_BITS); // atable[0] = '[]', so NIL is 0 xor TAG_ATM, which is just TAG_ATM.

var memory = new Array(HEAP_SIZE + STACK_SIZE + TRAIL_SIZE);
var code = [255];
var register = new Array(256);
var state;
var PDL = [];

// Stack for managing cleanup handlers needed during a cut
var cleanups = [];

/* Special purpose machine registers:

   P: Pointer to the next opcode to execute (in the code[] array)
  CP: Continuation Pointer. Points to the next code to execute if the current environment succeeds (basically the return address when calling a function)
mode: READ or WRITE depending on whether are matching or creating an exemplar on the heap
   H: Pointer to the next available heap cell
  HB: Pointer to where the heap should be truncated to if we backtrack
  TR: Pointer to the next available trail cell
   S: Pointer to the next symbol on the heap to match when unifying
   E: Pointer to the top environment frame   
   B: Pointer to the top choicepoint
  B0: Pointer to the choicepoint to return to after backtracking over a cut (ie the choicepoint created by the most recent call opcode)


  It is important to note that B and E do not point to the *next available* place to put an environment frame or choicepoint, but the *current* one.
*/
var debugging = true;
function debug_msg(msg)
{
    if (debugging)
        debug(msg);
}

function initialize()
{
    state = {H: 0,
             HB: 0,
             S: 0,
             P: 2,             
             CP: {code: bootstrap_code, 
                  predicate: null,
                  offset:1}, // halt
             B0: 0, // No backtrack frame
             B: 0,  // No backtrack frame
             E: HEAP_SIZE,
             TR: HEAP_SIZE + STACK_SIZE,
             mode: READ,
             running: true,
             foreign_retry: false,
             num_of_args: 0,
             S: 0,
             current_predicate: null};
    code = bootstrap_code;
}

function abort(why)
{        
    debug(why);
    throw why;
}

function bind(a, b)
{
    if (TAG(a) == TAG_REF && (TAG(b) != TAG_REF || VAL(b) < VAL(a)))
    {
        memory[VAL(a)] = b;
        trail(a);
    }
    else
    {
        memory[VAL(b)] = a;
        trail(b);
    }
}

function tidy_trail()
{
    t = memory[state.B + memory[state.B] + 5];
    if (t < HEAP_SIZE + STACK_SIZE)
        abort("Backtrack pointer " + state.B + " has garbage for TR: " + hex(t));
    while (t < state.TR)
    {
        if ((memory[t] < state.HB) || (state.H < memory[t] && memory[t] < state.B))
        {
            // This trailing is still required
            t = t + 1;
        }
        else
        {
            memory[t] = memory[state.TR - 1];
            state.TR = state.TR - 1;
        }
    }   
}

function trail(v)
{
    if (v < state.HB || (state.H < v && v < state.B))
    {
        memory[state.TR++] = v;
    }
    else
    {
    }
}

function unwind_trail(from, to)
{
    for (var i = from; i < to; i++)
    {
        memory[memory[i]] = memory[i] ^ (TAG_REF << WORD_BITS);
    }
}

// Returns boolean
function unify(a, b)
{
    PDL.push(a);
    PDL.push(b);
    var failed = false;
    while (PDL.length != 0 && !failed)
    {
        var d1 = deref(PDL.pop());
        var d2 = deref(PDL.pop());
        // if d1 == d2 then just proceed with the rest of the PDL. Otherwise we need to try and unify them, or fail
        if (d1 != d2)
        {
            type1 = TAG(d1);
            val1 = VAL(d1);
            type2 = TAG(d2);
            val2 = VAL(d2);          
            if (type1 == TAG_REF)
            {
                bind(d1, d2);
            }
            else
            {
                switch(type2)
                {
                case TAG_REF:
                    bind(d1, d2);
                    break;
                case TAG_ATM:
                case TAG_INT:
                    failed = true;
                    break;
                case TAG_FLT:
                    if (type1 == TAG_FLT) 
                    {
                        debug(floats[val1] + " vs " + floats[val2]);
                    }
                    failed = true;
                    break;
                case TAG_LST:
                    if (type1 == TAG_LST)
                    {                        
                        PDL.push(memory[val1]); // unify heads
                        PDL.push(memory[val2]);
                        PDL.push(memory[val1+1]); // unify tails
                        PDL.push(memory[val2+1]);
                    }
                    else
                        failed = true; // list and non-list
                    break;
                case TAG_STR:
                    if (type1 == TAG_STR)
                    {
                        f1 = VAL(memory[val1]);
                        f2 = VAL(memory[val2]);
                        if (f1 == f2)
                        {
                            for (var i = 0; i < ftable[f1][1]; i++)
                            {
                                PDL.push(val1 + 1 + i);
                                PDL.push(val2 + 1 + i);
                            }
                        }
                        else
                            failed = true; // different functors
                    }
                    else
                        failed = true; // str and atom/list
                }
            }
        }
    }
    return !failed;
}

function deref(p)
{
    while(TAG(p) == TAG_REF && VAL(p) != memory[VAL(p)])
    {
        q = memory[VAL(p)];
        if (q === undefined) // FIXME: Check that q =< p?
        {
            abort("Bad memory access: @" + p);
        }
        else
            p = q;
    }
    return p;
}

function explicit_deref(p)
{
    while(TAG(p) == TAG_REF && VAL(p) != memory[VAL(p)])
    {
        q = memory[VAL(p)];
        if (q === undefined)
        {
            abort("Bad memory access: @" + p);
        }
        else
            p = q;
    }
    return p;
}


// This should be a macro
function TAG(p)
{
    // >>> is unsigned-right-shift. Nice.
    return (p >>> WORD_BITS) & TAG_MASK;
}

// This should be a macro
function VAL(p)
{
    return p & ((1 << WORD_BITS)-1);
}

// Ideally this would be inlined, but javascript does not support macros. Ultimately this could be generated dynamically.
function backtrack()
{    
    if (state.B <= HEAP_SIZE)
    {
        return false;
    }
    state.B0 = memory[state.B + memory[state.B] + 7];
    // Also unwind any trailed bindings
    unwind_trail(memory[state.B + memory[state.B] + 5], state.TR);
    var next = memory[state.B + memory[state.B] + 4];
    state.P = next.offset;
    code = next.code;
    state.current_predicate = next.predicate;
    return true;
}

// Returns a <STR, f/n> cell. This MUST be followed (eventually) by n args. Attempting to print the term (or otherwise use) the term before then will result in chaos
// ftor must have the ATM tag!
function alloc_structure(ftor)
{
    var tmp = state.H;
    memory[state.H++] = ftor;
    return tmp ^ (TAG_STR << WORD_BITS);
}

function alloc_var()
{
    var result = state.H ^ (TAG_REF << WORD_BITS);
    memory[state.H] = result;    
    state.H++;
    return result;
}

function alloc_list()
{
    var result = (state.H+1) ^ (TAG_LST << WORD_BITS);
    memory[state.H] = result;    
    state.H++;
    return result;
}

function wam()
{
    state.running = true;
    while (state.running)
    {
        // Decode an instruction
        switch(code[state.P])
        {
        case 1: // allocate
            var tmpE;
            if (state.E > state.B)
            {
                tmpE = state.E + state.CP.code[state.CP.offset - 1] + 2;
            }
            else
            {
                tmpE = state.B + memory[state.B] + 8;
            }
            if (tmpE === undefined || isNaN(tmpE))
                abort("Top of frame is garbage: " + tmpE);
            if (tmpE < HEAP_SIZE || tmpE > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame exceeds bounds in allocate: " + hex(tmpE));

            // Save old environment and continuation
            memory[tmpE] = state.E;
            memory[tmpE + 1] = state.CP
            state.E = tmpE;
            state.P += 1;
            continue;

        case 2: // deallocate
            state.CP = memory[state.E + 1];
            if (memory[state.E] < HEAP_SIZE || memory[state.E] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame " + memory[state.E] + " exceeds bounds in deallocate. Environment is " + state.E + " P = " + state.P);

            state.E = memory[state.E];
            state.P += 1;
            continue;

        case 3: // call
            var predicate = predicates[code[state.P+1]];
            if (predicate !== undefined)
            {
                // Set CP to the next instruction so that when the predicate is finished executing we know where to come back to
                state.CP = {code: code,
                            predicate: state.current_predicate,
                            offset: state.P + 3};
                state.num_of_args = ftable[code[state.P+1]][1];
                state.B0 = state.B;
                state.current_predicate = predicate;
                code = predicate.clauses[predicate.clause_keys[0]].code;
                state.P = 0;
            }
            else if (foreign_predicates[code[state.P+1]] !== undefined)
            {
                state.num_of_args = ftable[code[state.P+1]][1];
                var fargs = new Array(state.num_of_args);
                for (i = 0; i < state.num_of_args; i++)
                {
                    fargs[i] = deref(register[i]);
                }
                // This is a bit counter-intuitive since it seems like we are never going to get a proceed to use the CP.
                // Remember that any time we might need CP to be saved, it will be. (If there is more than one goal, there will be an environment).
                // If there is only one goal (ie a chain rule) then we will be in exeucte already, not call.
                // This means it is never unsafe to set CP in a call port.
                // Further, rememebr that state.CP is used to create choicepoints (and environments), and since foreign frames may create these, we must set CP to
                // something sensible, even though we never expect to use it to actually continue execution from.
                state.CP = {code: code,
                            predicate: state.current_predicate,
                            offset:state.P + 3};
                result = foreign_predicates[code[state.P+1]].apply(null, fargs);
                state.foreign_retry = false;
                if (result)
                    state.P = state.P + 3;
                else if (!backtrack())
                    return false;
            }
            else
            {
                if (!undefined_predicate(code[state.P+1]))
                    return false;
            }
            continue;

        case 4: // execute
            var predicate = predicates[code[state.P+1]];
            if (predicate !== undefined)
            {
                // No need to save continuation for execute
                state.num_of_args = ftable[code[state.P+1]][1];
                state.B0 = state.B;
                state.current_predicate = predicate;
                code = predicate.clauses[predicate.clause_keys[0]].code;
                state.P = 0;
            }
            else if (foreign_predicates[code[state.P+1]] !== undefined)
            {
                state.num_of_args = ftable[code[state.P+1]][1];
                var fargs = new Array(state.num_of_args);
                for (i = 0; i < state.num_of_args; i++)
                    fargs[i] = deref(register[i]);
                result = foreign_predicates[code[state.P+1]].apply(null, fargs);
                state.foreign_retry = false;
                if (result)
                {
                    state.current_predicate = state.CP.predicate;
                    code = state.CP.code;
                    state.P = state.CP.offset;
                }
                else if (!backtrack())
                    return false;
            }
            else
            {
                if (!undefined_predicate(code[state.P+1]))
                    return false;
            }
            continue;

        case 5: // proceed
            state.P = state.CP.offset;
            state.current_predicate = state.CP.predicate;
            code = state.CP.code;
            continue;

        case 6: // put_variable: Initialize a new variable in Yn, and also put it into Ai
            register_location = state.E + code[state.P+1] + 2;
            memory[register_location] = register_location ^ (TAG_REF << WORD_BITS);
            register[code[state.P+2]] = register_location ^ (TAG_REF << WORD_BITS);
            state.P += 3;
            continue;

        case 7: // put_variable: Put fresh var into registers Ai and Xn
            var freshvar = state.H ^ (TAG_REF << WORD_BITS);
            memory[state.H] = freshvar;
            register[code[state.P+1]] = freshvar;
            register[code[state.P+2]] = freshvar;
            state.H++;
            state.P += 3;
            continue;

        case 8: // put_value
            var source;
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                if (memory[register_location] === undefined)
                    abort("Invalid memory access in put_value");
                register[code[state.P+3]] = memory[register_location];
            }
            else
            {
                register[code[state.P+3]] = register[code[state.P+2]];
            }
            state.P += 4;
            continue;

        case 9: // put_unsafe_value
            register_location = state.E + code[state.P+1] + 2;
            // This is the unsafe bit. If the value now in register[code[state.P+2]] is on the stack (that is, it is > E) then we have to push a new variables
            // onto the stack to avoid dangling references to things that are about to be cleaned up
            if (memory[register_location] < state.E)
            {
                // No, so we can just behave like put_value
                register[code[state.P+2]] = deref(memory[register_location])
            }
            else
            {
                // Yes, so we need to push a new variable instead
                var v = alloc_var();
                bind(v, memory[register_location]);
                register[code[state.P+2]] = v;
            }
            state.P += 3;
            continue;

        case 10: // put_constant C into Ai            
            register[code[state.P+2]] = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            state.P += 3;
            continue;

        case 11: // put_nil into Ai
            register[code[state.P+1]] = NIL;
            state.P += 2;
            continue;

        case 12: // put_structure
            register[code[state.P+2]] = alloc_structure(code[state.P+1] ^ (TAG_ATM << WORD_BITS));
            state.mode = WRITE;
            state.P += 3;
            continue;

        case 13: // put_list
            register[code[state.P+1]] = alloc_list();
            state.mode = WRITE;
            state.P += 2;
            continue;

        case 14: // put_integer I into Ai
            register[code[state.P+2]] = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
            state.P += 3;
            continue;           

        case 15: // get_variable
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                memory[register_location] = register[code[state.P+3]];
            }
            else
            {
                register[code[state.P+2]] = register[code[state.P+3]];
            }
            state.P+= 4;
            continue;
            
        case 16: // get_value
            var source;
            var target = register[code[state.P+3]];
            gc_check(target);
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                source = memory[register_location];
            }
            else
            {
                source = register[code[state.P+2]];
            }
            state.P += 4;
            if (!unify(source, target))
                if (!backtrack())
                    return false;
            continue;

        case 17: // get_constant C from Ai            
            // First, get what is in Ai into sym
            var sym = deref(register[code[state.P+2]]);
            // Then get arg. This is an atom index, not a <CON, i> cell. It needs to be made into the latter!
            var arg = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(bar) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                if (!backtrack())
                    return false;
            }
            continue;

        case 18: // get_nil
            var sym = deref(register[code[state.P+1]]);
            state.P += 1;
            if (TAG(sym) == TAG_REF)
                bind(sym, NIL);
            else if (sym != NIL)
                if (!backtrack())
                    return false;
            continue;
            

        case 19: // get_structure
            var ftor = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            var addr = deref(register[code[state.P+2]]);
            state.P += 3;
            if (TAG(addr) == TAG_REF)
            {
                state.mode = WRITE;
                a = alloc_structure(ftor);
                bind(memory[addr], a);
            }
            else if (TAG(addr) == TAG_STR && memory[VAL(addr)] == ftor)
            {
                state.mode = READ;
                state.S = VAL(addr)+1;
            }                        
            else
            {
                if (!backtrack())
                    return false;
            }
            continue;

        case 20: // get_list from Ai
            var addr = deref(register[code[state.P+1]]);
            state.P += 2;
            if (TAG(addr) == TAG_REF)
            {
                // predicate called with var and we are expecting a list
                var l = state.H ^ (TAG_LST << WORD_BITS);
                bind(memory[addr], l);
                state.mode = WRITE;
            }
            else if (TAG(addr) == TAG_LST)
            {   
                state.S = VAL(addr);
                state.mode = READ;                
            }
            else
                if (!backtrack())
                    return false;
            continue;

        case 21: // get_integer I from Ai            
            // First, get what is in Ai into sym
            var sym = deref(register[code[state.P+2]]);
            // Then get arg. This is the actual integer, not a <INT, i> cell. It needs to be made into the latter!
            var arg = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(7) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                if (!backtrack())
                    return false;
            }
            continue;

        case 22: // unify_void
            if (state.mode == READ)
                state.S += code[state.P+1];
            else
                for (i = 0; i < code[state.P+1]; i++)
                    alloc_var();
            state.P += 2;
            continue;

        case 23: //unify_variable
            var source;
            if (state.mode == READ) // If reading, consume the next symbol
            {                
                source = memory[state.S++]; 
            }
            else
            {
                source = alloc_var(); // If writing, create a new var
            }
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                // GC: This needs to be trailed if state.B is not 0, apparently
                bind(memory[register_location], source);
            }
            else
            {
                register[code[state.P+2]] = source;
            }
            state.P += 3;
            continue;

        case 24: // unify_value
            var did_fail = false;
            if (state.mode == READ)
            {
                source = memory[state.S++];
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    did_fail = !unify(memory[register_location], source);
                }
                else
                {
                    did_fail = !unify(register[code[state.P+2]], source);
                }
            }
            else
            {
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    memory[state.H++] = memory[register_location];
                }
                else
                {
                    memory[state.H++] = register[code[state.P+2]];
                }
            }
            state.P += 3;
            if (did_fail)
                if (!backtrack())
                    return false;
            continue;
        case 25: // unify_local_value
            var did_fail = false;
            if (state.mode == READ)
            {
                source = memory[state.S++];
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    did_fail = !unify(memory[register_location], source);
                }
                else
                {
                    did_fail = !unify(register[code[state.P+2]], source);
                }
           }
            else
            {
                var addr;
                if (code[state.P+1] == 0) // Y-register;
                {
                    register_location = state.E + code[state.P+2] + 2;
                    addr = memory[register_location];
                }
                else
                {
                    addr = register[code[state.P+2]];                    
                }
                addr = deref(addr);
                if (VAL(addr) < state.H)
                {
                    // Address is on the heap. Just push the value onto the top of the heap
                    memory[state.H++] = addr;
                }
                else
                {
                    // Address is on the stack. Push a new variable onto the heap and bind to the value
                    fresh = state.H ^ (TAG_REF << WORD_BITS);
                    memory[state.H++] = fresh;
                    bind(fresh, addr);
                    if (code[state.P+1] == 1)
                        register[code[state.P+2]] = fresh; // also set X(i) if X-register
                }
            }
            state.P += 3;
            if (did_fail)
                if (!backtrack())
                    return false;
            continue;
        case 26: // unify_constant
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
                state.P += 2;
                if (TAG(sym) == TAG_REF)
                {
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
                state.P += 2;
            }
            continue;
        case 27: // unify_integer
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS)
                state.P += 2;
                if (TAG(sym) == TAG_REF)
                {
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
                state.P += 2;
            }
            continue;

        case 28: // try_me_else
            // We need to allocate a new choicepoint, but first we need to determine /where/ to put it, since we do not keep a reference to the top of the stack.
            // The last item on the stack is either an environment, or a choicepoint.
            var newB;
            if (state.E > state.B)
            {
                // In this case, it is an environment. In the real WAM, which does stack trimming (see Ait-Kaci chapter 5.7), we only have CE, CP and then N saved Y-registers. 
                // Therefore, we need to write the new choicepoint at 2 + N. What is N, though? Well, it turns out N gets gradually smaller as time goes on, which
                // is why it is not stored in the frame itself. If call(f) is outfitted with a second argument to become call(f, n) then we can decode this in try_me_else
                // (and ignore it if we did not want to create a new environment) by looking at CP, which points to the instruction after the call() opcode. Therefore,
                // code[CP-1] ought to be N.

                // -----------
                // |0  | CE  |
                // |1  | CP  |
                // |3  | Y0  |
                //  ...
                // |n+2| Yn  |
                // -----------
                newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
            }
            else
            {   
                // In this case, the top frame is a choicepoint. This is a bit easier: A choicepoint contains 7 saved special-purpose registers, the N root arguments
                // for the goal, and, happily, the value of N as the very first argument. Therefore, we can read the 0th entry of the current frae (at state.B)
                // and add 9 to it to get the top of the stack.
                newB = state.B + memory[state.B] + 8;                
            }
            memory[newB] = state.num_of_args;
            var n = memory[newB];
            for (i = 0; i < n; i++)
            {
                memory[newB + i + 1] = register[i];
            }
            // Save the current context
            memory[newB+n+1] = state.E;
            memory[newB+n+2] = state.CP;
            memory[newB+n+3] = state.B;
            var next = code[state.P+1];
            if ((next & 0x80000000) == 0)
            {
                // next is a clause index in the current predicate
                memory[newB+n+4] = {code: state.current_predicate.clauses[next].code, 
                                    predicate:state.current_predicate, 
                                    offset:0};
            }
            else
            {
                
                // next is an absolute address in the current clause: Used for auxiliary clauses only
                memory[newB+n+4] = {code: code, 
                                    predicate: state.current_predicate,
                                    offset:next ^ 0x80000000};
            }
            //memory[newB+n+4] = {code: code, offset:code[state.P+1]};
            memory[newB+n+5] = state.TR;
            memory[newB+n+6] = state.H;
            memory[newB+n+7] = state.B0;
            state.B = newB;
            state.HB = state.H;
            state.P += 2;
            continue;

        case 29: // retry_me_else
            // Unwind the last goal. The arity if the first thing on the stack, then the saved values for A1...An
            var arity = memory[state.B];
            for (var i = 0; i < arity; i++)
                register[i] = memory[state.B + i + 1];
            // Now restore all the special-purpose registers
            if (memory[state.B + arity + 1] < HEAP_SIZE)
                abort("Top of frame contains E which is in the heap");
            if (memory[state.B + arity + 1] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame contains E which exceeds the stack");
            state.E = memory[state.B + arity + 1];       
            state.CP = memory[state.B + arity + 2];      
            var next = code[state.P+1];
            // set up the 'else' part of retry_me_else by adjusting the saved value of B            
//            memory[state.B + arity + 4] = {code: state.current_predicate.clauses[state.current_predicate.clause_keys[code[state.P+1]]].code, predicate:state.current_predicate, offset:0};
            if ((next & 0x80000000) == 0)                
            {
                // next is a clause index in the current predicate
                memory[state.B+arity+4] = {code: state.current_predicate.clauses[next].code, 
                                           predicate:state.current_predicate, 
                                           offset:0};
            }
            else
            {
                // next is an absolute address in the current clause: Used for auxiliary clauses only
                memory[state.B+arity+4] = {code: code, 
                                           predicate: state.current_predicate,
                                           offset:next ^ 0x80000000};
            }
            unwind_trail(memory[state.B + arity + 5], state.TR);

            state.TR = memory[state.B + arity + 5];
            state.H = memory[state.B + arity + 6];
            state.HB = state.H
            state.P += 2;
            continue;
            
        case 30: // trust_me
            // Unwind the last goal. The arity if the first thing on the stack, then the saved values for A1...An
            var n = memory[state.B];
            for (var i = 0; i < n; i++)
            {
                register[i] = memory[state.B + i + 1];
            }
            // Now restore all the special-purpose registers
            if (memory[state.B + n + 1] < HEAP_SIZE || memory[state.B + n + 1] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame exceeds bounds in trust. Read from memory[" + (state.B+n+1) + "]. State.B is " + state.B);
            state.E = memory[state.B + n + 1];            
            state.CP = memory[state.B + n + 2];            
            unwind_trail(memory[state.B + n + 5], state.TR);
            state.TR = memory[state.B + n + 5];
            state.H = memory[state.B + n + 6];
            state.B = memory[state.B + n + 3];
            state.HB = memory[state.B+ memory[state.B] + 6];
            //state.HB = memory[state.B + n + 6];
            state.P += 2;
            continue;

        case 31: // neck_cut
            // Move B back to B0 and tidy the trail. If B == B0 then do nothing (ie if there is a useless cut in the only clause of a predicate)
            var result = true;
            if (state.B > state.B0)
            {
                while (cleanups[0] !== undefined && cleanups[0].B > state.B0 && cleanups[0].B < state.B)
                {
                    result = run_cleanup(cleanups[0]) && result;
                    cleanups.shift();
                }
                state.B = state.B0;
                if (state.B > 0)
                    tidy_trail();                
            }
            if (result)
                state.P += 1;
            else if (!backtrack())
                return false;
            continue;

        case 32: // cut(I)
            y = VAL(memory[state.E + 2 + code[state.P+1]]);
            var result = true;
            if (state.B > y)
            {
                while (cleanups[0] !== undefined && cleanups[0].B > y && cleanups[0].B < state.B0)
                {
                    result = run_cleanup(cleanups[0]) && result;
                    cleanups.shift();
                }    
                state.B = y;
                if (state.B > 0)
                    tidy_trail();
            }
            else
            {
            }
            if (result)
                state.P += 2;
            else if (!backtrack())
                return false;
            continue;

        case 33: // get_level(I)
            memory[state.E + 2 + code[state.P+1]] = state.B0 ^ (TAG_INT << WORD_BITS);
            state.P += 2;
            continue;

        case 40: // call_aux
            var offset = code[state.P+1];
            state.CP = {code:code,
                        predicate: state.current_predicate,
                        offset:state.P + 4};
            state.num_of_args = code[state.P+2];
            state.P = offset;
            state.B0 = state.B;
            continue;

        case 41: // execute_aux
            var offset = code[state.P+1];
            state.num_of_args = code[state.P+2];
            state.P = offset;
            state.B0 = state.B;            
            continue;

        case 42: // retry_foreign
            state.foreign_value = memory[state.B+1];
            state.P = memory[state.B+2].offset;
            code = memory[state.B+2].code;
            state.current_predicate = memory[state.B+2].current_predicate;
            var n = memory[state.B];
            state.foreign_retry = true;
            for ( i = 0; i < n-2; i++)
            {
                register[i] = memory[state.B+3+i];
            }
            state.E = memory[state.B + n + 1];
            state.CP = memory[state.B + n + 2];      
            unwind_trail(memory[state.B + n + 5], state.TR);
            state.TR = memory[state.B + n + 5];
            state.H = memory[state.B + n + 6];
            state.HB = state.H
            continue;
        case 43: // get_choicepoint
            var i = code[state.P+1];
            var choice = state.B;
            while (i != 0)
            {
                choice = memory[choice + memory[choice] + 3];
                i--;
            }
            
            memory[state.E + 2 + code[state.P+2]] = (choice ^ TAG_INT << WORD_BITS);
            state.P += 3;
            continue;            
            
         // All the floating point operations are here because I added them as an afterthought!
        case 50: // get_float I from Ai            
            var sym = deref(register[code[state.P+2]]);
            var arg = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(7) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                if (!backtrack())
                    return false;
            }
            continue;
        case 51: // put_float I into Ai
            register[code[state.P+2]] = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
            state.P += 3;
            continue;           
        case 52: // unify_float
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
                state.P += 2;
                if (TAG(sym) == TAG_REF)
                {
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
                state.P += 2;
            }
            continue;

        case 60: // put_variable Yn
            // Note that this is different from put_variable(Yn, Ai) in that it ONLY puts a fresh variable into Yn
            // This is needed to make garbage collection safe
            register_location = state.E + code[state.P+1] + 2;
            memory[register_location] = register_location ^ (TAG_REF << WORD_BITS);
            state.P += 2;
            continue;

            

        case 254: // Only clause: NOP
            state.P += 2;
            continue;
        case 255: // halt
            state.running = false;
            continue;
        default:
            abort("unexpected opcode at P=" + (((state.current_predicate == null)?("no predicate"):(atable[ftable[state.current_predicate.key][0]] + "/" + ftable[state.current_predicate.key][1])) + "@" + state.P + ": " + code[state.P]));
        }        
    }
    return true;
}


/* Testing */

function hex(number)
{
    if (number == undefined)
        return "undefined";
    if (number < 0)
    {
    	number = 0xFFFFFFFF + number + 1;
    }
    return "0x" + number.toString(16).toUpperCase();
}

function allocate_first_frame()
{
    // Allocate an environment for the toplevel?
    state.E = HEAP_SIZE; 
    memory[state.E] = 0;     // previous environment = NULL
    memory[state.E + 1] = state.CP;
}

function term_to_string(t)
{
    return format_term(t, {ignore_ops:false, quoted: true, numbervars: false});
}

function copy_state(s)
{
    return {H: s.H,
            HB: s.HB,
            S: s.S,
            P: s.P,
            CP: s.CP, 
            B0: s.B0,
            B: s.B,
            E: s.E,
            TR: s.TR,
            mode: s.mode,
            running: s.running,
            num_of_args: s.num_of_args,
            foreign_retry: s.foreign_retry,
            current_predicate: s.current_predicate};
}

function copy_registers(r)
{
    return r.slice(0);
}


function run_cleanup(c)
{
    var saved_state = copy_state(state);
    var saved_registers = copy_registers(register);
    var saved_code = code;
    state.P = c.P;
    register = c.V.slice(0);
    code = c.code;
    debugging = true;
    var result = true;

    if (!wam())
    {
        // Failure is ignored, but exceptions are raised
        if (exception != null)
            result = false;
    }
    register = copy_registers(saved_registers);
    var saved_heap = state.H;
    state = copy_state(saved_state);
    state.H = saved_heap;
    code = saved_code;
    return result;
}

// Exceptions are implement as per Bart Demoen's 1989 paper
// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.57.4354&rep=rep1&type=pdf
function predicate_throw(t)
{
    exception = record_term(t);
    return unwind_stack();
}

function unwind_stack()
{
    if (state.block === undefined)
    {
        abort("Uncaught exception: " + term_to_string(recall_term(exception, {})));
    }
    state.B = state.block;
    return false;
}

function get_current_block(b)
{
    return unify(b, state.block ^ (TAG_INT << WORD_BITS));
}

function install_new_block(nb)
{
    state.block = state.B;
    return unify(nb, state.B ^ (TAG_INT << WORD_BITS));
}

function reset_block(x)
{
    state.block = VAL(x);
    return true;
}

function clean_up_block(nb)
{
    // If alternative to B is nb, then select it now
    if (memory[state.B+memory[state.B]+4] == VAL(nb))
        state.B = VAL(memory[VAL(nb)+memory[VAL(nb)]+4]);
    return true;

}
function get_exception(e)
{
    if (exception !== null)
    {
        return unify(e, recall_term(exception, {}));
    }
    else
    {
        return false;
    }
}

function clear_exception()
{
    exception = null;
    return true;
}

function undefined_predicate(ftor)
{
    if (prolog_flag_values.unknown == "error")
    {
        var indicator = state.H ^ (TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor("/", 2);
        memory[state.H++] = ftable[ftor][0] ^ (TAG_ATM << WORD_BITS);
        memory[state.H++] = ftable[ftor][1] ^ (TAG_INT << WORD_BITS);
        existence_error("procedure", indicator);
    }
    else if (prolog_flag_values.unknown == "warning")
    {
        stdout("Undefined predicate " + atable[ftable[ftor][0]] + "/" + ftable[ftor][1] + "\n");
    }
    if (!backtrack())
    {
        debug("Could not backtrack");
        return false;
    }
    return true;
}

// End exceptions code

// /System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Resources/jsc foreign.js wam.js bootstrap.js -e "demo()"
function demo(d)
{
    debugging = d;
    load_state();
    stdout("Loaded " + Object.keys(predicates).length + " predicates\n");
    stdout("Loaded " + atable.length + " atoms\n");
    stdout("Loaded " + ftable.length + " functors\n");
    initialize();
    allocate_first_frame();

    var ftor = VAL(lookup_functor("toplevel", 0));
    state.P = 0;
    var pred = predicates[ftor];
    var pi = predicates[ftor].clause_keys[0];
    state.current_predicate = pred;
    code = pred.clauses[pi].code;
    if (wam())
        stdout("Succeeded\n");
    else if (exception == null)
        stdout("Failed\n");
    else
        stdout("Uncaught exception: " + term_to_string(recall_term(exception, {})) +"\n");
}


function unit_tests(d)
{
    debugging = d;
    load_state();
    stdout("Loaded " + Object.keys(predicates).length + " predicates\n");
    stdout("Loaded " + atable.length + " atoms\n");
    stdout("Loaded " + ftable.length + " functors\n");
    initialize();
    allocate_first_frame();

    var ftor = VAL(lookup_functor("toplevel", 0));
    state.P = 0;
    var pred = predicates[ftor];
    var pi = predicates[ftor].clause_keys[0];
    state.current_predicate = pred;
    code = pred.clauses[pi].code;
    if (wam())
        stdout("Succeeded\n");
    else if (exception == null)
        stdout("Failed\n");
    else
        stdout("Uncaught exception: " + term_to_string(recall_term(exception, {})) +"\n");
}


function reset_compile_buffer()
{
    compile_buffer = [];
    return true;
}
// File read.js
/* Term reading */
// See http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
// Parsers return either:
// 1) An string, in case of an atom
// 2) An integer, in case of an integer
// 3) An object with .list and .tail if a list (because apparently it is not easy to determine if the type of something is a list at runtime!?)
//      If it is a proper list, .tail == NIL
// 4) An object with .variable_name, if a variable
// 5) An object with .functor (a string) and .args (an array) defined if a term

function parse_infix(s, lhs, precedence)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    token = token.value;
    var rhs = {};
    if (!read_expression(s, precedence, false, false, rhs))
        return false;
    return {functor: token,
            args: [lhs, rhs.value]};
}

function parse_postfix(s, lhs)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    return {functor: token.value,
            args: [lhs]};
}

// A reminder: yfx means an infix operator f, with precedence p, where the lhs has a precendece <= p and the rhs has a precedence < p.

var prefix_operators = {":-": {precedence: 1200, fixity: "fx"},
                        "?-": {precedence: 1200, fixity: "fx"},
                        "dynamic": {precedence: 1150, fixity: "fx"},
                        "discontiguous": {precedence: 1150, fixity: "fx"},
                        "initialization": {precedence: 1150, fixity: "fx"},
                        "meta_predicate": {precedence: 1150, fixity: "fx"},
                        "module_transparent": {precedence: 1150, fixity: "fx"},
                        "multifile": {precedence: 1150, fixity: "fx"},
                        "thread_local": {precedence: 1150, fixity: "fx"},
                        "volatile": {precedence: 1150, fixity: "fx"},
                        "\+": {precedence: 900, fixity: "fy"},
                        "~": {precedence: 900, fixity: "fx"},
                        "?": {precedence: 500, fixity: "fx"},
                        "+": {precedence: 200, fixity: "fy"},
                        "-": {precedence: 200, fixity: "fy"},
                        "\\": {precedence: 200, fixity: "fy"}};


var infix_operators = {":-": {precedence: 1200, fixity: "xfx"},
                       "-->": {precedence: 1200, fixity: "xfx"},
                       ";": {precedence: 1100, fixity: "xfy"},
                       "|": {precedence: 1100, fixity: "xfy"},
                       "->": {precedence: 1050, fixity: "xfy"},
                       "*->": {precedence: 1050, fixity: "xfy"},
                       ",": {precedence: 1000, fixity: "xfy"},
                       ":=": {precedence: 990, fixity: "xfx"},
                       "<": {precedence: 700, fixity: "xfx"},
                       "=": {precedence: 700, fixity: "xfx"},
                       "=..": {precedence: 700, fixity: "xfx"},
                       "=@=": {precedence: 700, fixity: "xfx"},
                       "=:=": {precedence: 700, fixity: "xfx"},
                       "=<": {precedence: 700, fixity: "xfx"},
                       "==": {precedence: 700, fixity: "xfx"},
                       "=\=": {precedence: 700, fixity: "xfx"},
                       ">": {precedence: 700, fixity: "xfx"},
                       ">=": {precedence: 700, fixity: "xfx"},
                       "@<": {precedence: 700, fixity: "xfx"},
                       "@=<": {precedence: 700, fixity: "xfx"},
                       "@>": {precedence: 700, fixity: "xfx"},
                       "@>=": {precedence: 700, fixity: "xfx"},
                       "\=": {precedence: 700, fixity: "xfx"},
                       "\==": {precedence: 700, fixity: "xfx"},
                       "is": {precedence: 700, fixity: "xfx"},
                       ">:<": {precedence: 700, fixity: "xfx"},
                       ":<": {precedence: 700, fixity: "xfx"},
                       ":": {precedence: 600, fixity: "xfy"},
                       "+": {precedence: 500, fixity: "yfx"},
                       "-": {precedence: 500, fixity: "yfx"},
                       "/\\": {precedence: 500, fixity: "yfx"},
                       "\\/": {precedence: 500, fixity: "yfx"},
                       "xor": {precedence: 500, fixity: "yfx"},
                       "*": {precedence: 400, fixity: "yfx"},
                       "/": {precedence: 400, fixity: "yfx"},
                       "//": {precedence: 400, fixity: "yfx"},
                       "rdiv": {precedence: 400, fixity: "yfx"},
                       "<<": {precedence: 400, fixity: "yfx"},
                       ">>": {precedence: 400, fixity: "yfx"},
                       "mod": {precedence: 400, fixity: "yfx"},
                       "rem": {precedence: 400, fixity: "yfx"},
                       "**": {precedence: 200, fixity: "xfx"},
                       "^": {precedence: 200, fixity: "xfy"}};

// This returns a javascript object representation of the term. It takes the two extra args because of some oddities with Prolog:
// 1) If we are reading foo(a, b) and we are at the a, we would accept the , as part of the LHS. ie, we think (a,b) is the sole argument. Instead, we should make , have
//    very high precedence if we are reading an arg. Of course, () can reduce this again, so that foo((a,b)) does indeed read ,(a,b) as the single argument
// 2) | behaves slightly differently in lists, in a similar sort of way
function read_expression(s, precedence, isarg, islist, expression)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    token = token.value;
    if (token == null)
    {        
        expression.value = {end_of_file:true};
        return true;
    }
    var lhs;
    // Either the token is an operator, or it must be an atom (or the start of a list or curly-list)
    var op = prefix_operators[token];
    if (op === undefined)
    {  
        if (token == "\"")
        {
            // We have to just read chars until we get a close " (taking care with \" in the middle)
            var args = [];
            var t = 0;
            var mode = 0;
            if (prolog_flag_values['double_quotes'] == "chars")
                mode = 0;
            else if (prolog_flag_values['double_quotes'] == "codes")
                mode = 1;
            else if (prolog_flag_values['double_quotes'] == "atom")
                mode = 2;
            while (true)
            {
                t = get_raw_char_with_conversion(s.stream);
                if (t == '"')
                    break;
                if (t == "\\")
                {
                    if (peek_raw_char_with_conversion(s.stream) == '"')
                    {
                        get_raw_char_with_conversion(s.stream);
                        if (mode == 1)
                            args.push('"'.charCodeAt(0));
                        else
                            args.push('"');
                        continue;
                    }
                }
                if (mode == 1)
                    args.push(t.charCodeAt(0));                
                else
                    args.push(t);
            }
            if (mode == 2)
                lhs = args.join('');
            else
                lhs = {list: args, tail: "[]"};
        }
        else if (token == "[" || token == "{")
        {
            // The principle for both of these is very similar
            var args = [];
            var next = {};
            while(true)
            {
                var t = {};
                if (!read_expression(s, Infinity, true, true, t))
                    return false;
                t = t.value;
                if (t == "]")
                {
                    lhs = "[]";
                    break;
                    // Special case for the empty list, since the first argument is ']'
                }
                args.push(t);
                next = {};
                if (!read_token(s, next))
                    return false;               
                next = next.value;
                if (next == ',')
                    continue;
                else if (next == "]" && token == "[")
                {
                    lhs = {list: args, tail: "[]"};
                    break;
                }
                else if (next == "}" && token == "{")
                {
                    lhs = {functor: "{}", args:args};
                    break;
                }
                else if (next == "|" && token == "[")
                {
                    var tail = {};
                    if (!read_expression(s, Infinity, true, true, tail))
                        return false;
                    lhs = {list: args, tail: tail.value},
                    next = {};
                    if (!read_token(s, next))
                        return false;
                    next = next.value;
                    if (next == "]")
                        break;
                    else
                        return syntax_error("missing ]");
                }
                else
                    return syntax_error("mismatched " + token + " at " + next);
            }
        }
        else if (token == "(")
        {
            // Is this right? () just increases the precedence to infinity and reads another term?
            var lhs = {};
            if (!read_expression(s, Infinity, false, false, lhs))
                return false;
            lhs = lhs.value;
            next = {};
            if (!read_token(s, next))
                return false;
            next = next.value;
            if (next != ")")
                return syntax_error("mismatched ( at " + next);
        }
        else
        {
            // It is an atom
            lhs = token;
        }
    }
    else if (op.fixity == "fx")
    {
        var arg = {};
        if (!read_expression(s, op.precedence, isarg, islist, arg))
            return false;
        lhs = {functor: token, args:[arg.value]};
    }
    else if (op.fixity == "fy")
    {
        var arg = {};
        if (!read_expression(s, op.precedence+0.5, isarg, islist, arg))
            return false;
        lhs = {functor: token, args:[arg.value]};
    }
    else
        return false; // Parse error    
    while (true)
    {
        var infix_operator = {};
        if (!peek_token(s, infix_operator))
            return false;
        infix_operator = infix_operator.value;
        if (typeof(infix_operator) == "number" && infix_operator <= 0)
        {
            // Yuck. This is when we read something like X is A-1. Really the - is -/2 in this case
            read_token(s, {});
            unread_token(s, Math.abs(infix_operator));
            unread_token(s, "-");
            infix_operator = "-";
        }
        if (infix_operator == '(')
        {
            // We are reading a term. Keep reading expressions: After each one we should
            // either get , or )
            // First though, consume the (
            read_token(s, {});
            var args = [];
            var next = {};
            while (true)
            {
                var arg = {};
                if (!read_expression(s, Infinity, true, false, arg))
                    return false;
                args.push(arg.value);
                next = {};
                if (!read_token(s, next))
                    return false;
                next = next.value;
                if (next == ')')
                    break;
                else if (next == ',')
                    continue;
                else
                {
                    if (next == null)
                        return syntax_error("end_of_file");
                    else
                        return syntax_error(next);
                }
            }
            // ./2 is a list
            if (lhs == "." && args.length == 2)
            {
                lhs = {list: args[0],
                       tail: args[1]};
            }
            else
            {
                lhs = {functor: lhs,
                       args:args};
            }
            // Now, where were we?
            infix_operator = {};
            if (!peek_token(s, infix_operator))
                return false;
            infix_operator = infix_operator.value;
        }
        // Pretend that . is an operator with infinite precedence
        if (infix_operator == ".")
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == "," && isarg)
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == "|" && islist)
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == null)
        {
            expression.value = lhs;
            return true;
        }            
        op = infix_operators[infix_operator];
        if (op !== undefined)
        {
            if (op.fixity == "xfx" && precedence > op.precedence)
            {
                lhs = parse_infix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "xfy" && precedence > op.precedence)
            {
                // Is this 0.5 thing right? Will it eventually drive up precedence to the wrong place? We never want to reach the next integer...
                lhs = parse_infix(s, lhs, op.precedence+0.5); 
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "yfx" && precedence >= op.precedence)
            {
                lhs = parse_infix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "xf" && precedence > op.precedence)
            {
                lhs = parse_postfix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "yf" && precedence >= op.precedence)
            {
                lhs = parse_postfix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else
            {
                expression.value = lhs;
                return true;
            }
        }
        else
        {
            expression.value = lhs;
            return true;
        }
    }
}

function parse_term_options(options)
{
    var result = {};
    var yes = lookup_atom("true");
    while (options != NIL)
    {
        if (TAG(options) != TAG_LST)
            return type_error("list", options);
        var head = memory[VAL(options)];
        if (TAG(head) != TAG_STR)
            return type_error("option", head);
        var ftor = memory[VAL(head)];
        if (ftor == lookup_functor("quoted",1))
        {
            result.quoted = (memory[VAL(head)+1] == yes)
        } 
        else if (ftor == lookup_functor("ignore_ops",1))
        {
            result.ignore_ops = (memory[VAL(head)+1] == yes)
        }
        else if (ftor == lookup_functor("numbervars",1))
        {
            result.numbervars = (memory[VAL(head)+1] == yes)
        }
        else if (ftor == lookup_functor("variables",1))
        {
            result.variables = memory[VAL(head)+1];
        }
        else if (ftor == lookup_functor("variable_names",1))
        {
            result.variable_names = memory[VAL(head)+1];
        }
        else if (ftor == lookup_functor("singletons",1))
        {
            result.singletons = memory[VAL(head)+1];
        }
        else
        {
            return type_error(option, head);
        }
        options =  memory[VAL(options)+1];
    }
    return result;
}

function read_term(stream, term, options)
{
    if (!(options = parse_term_options(options)))
        return false;
    var streamindex = VAL(get_arg(stream, 1));
    var s = streams[streamindex];
    var context = {stream:s, peeked_token: undefined};
    var expression = {};
    if (!read_expression(context, Infinity, false, false, expression))
        return false;
    expression = expression.value;
    // Depending on the situation, we may expect a . now on the stream. 
    // There will not be one if we are going to return end_of_file because it is actually the eof
    // (Of course, if the file contains end_of_file. then we will return end_of_file AND read the .
    // Luckily we can distinguish the two cases
    // There will also not be one if we are in atom_to_term mode, which is not yet implemented    
    if (expression.end_of_file === undefined)
    {
        var period = {};
        if (!read_token(context, period))
            return false;
        if (period.value != ".") // Missing period === eof
            return syntax_error("end_of_file");
    }
    else
        expression = "end_of_file";
    
    var varmap = {};
    var singletons = {};
    t1 = expression_to_term(expression, varmap, singletons);
    var rc = 1;
    if (options.variables !== undefined || options.singletons !== undefined)
    {
        var equals2 = lookup_functor("=", 2);
        var keys = Object.keys(varmap);
        for (var i = 0; i < keys.length; i++)
        {
            var varname = keys[i];
            if (options.variables !== undefined)
            {                
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.variables))
                    return false;
                memory[state.H] = varmap[varname];
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.variables = memory[state.H+1];
                state.H+=2;
            }
            if (options.variable_names !== undefined)
            {                
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.variable_names))
                {
                    debug("not unifiable: " + term_to_string(options.variable_names));
                    return false;
                }
                memory[state.H] = (state.H+2) ^ (TAG_STR << WORD_BITS);
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.variable_names = memory[state.H+1];
                memory[state.H+2] = equals2;
                memory[state.H+3] = lookup_atom(varname);
                memory[state.H+4] = varmap[varname];
                state.H+=5;
            }
        }
        if (options.variables !== undefined)
            if (!unify(options.variables, NIL))
                return false;
        if (options.variable_names !== undefined)
            if (!unify(options.variable_names, NIL))
                return false;       
    }
    if (options.singletons !== undefined)
    {
        var keys = Object.keys(singletons);
        for (var i = 0; i < keys.length; i++)
        {
            var varname = keys[i];
            if (singletons[varname] == 1)
            {
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.singletons))
                    return false;
                memory[state.H] = (state.H+2) ^ (TAG_STR << WORD_BITS);
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.singletons = memory[state.H+1];
                memory[state.H+2] = equals2;
                memory[state.H+3] = lookup_atom(varname);
                memory[state.H+4] = varmap[varname];
                state.H+=5;
            }
        }
        if (!unify(options.singletons, NIL))
            return false;      
    }
    return unify(term, t1);
}

function predicate_write_term(stream, term, options)
{
    if (!(options = parse_term_options(options)))
        return false;
    var value = format_term(term, options);
    var s = {};
    if (!get_stream(stream, s))
        return false;
    s = s.value;
    if (s.write == null)
        return permission_error("output", "stream", stream);
    
    var bytes = toByteArray(value);
    return (s.write(s, 1, bytes.length, bytes) >= 0)
}

function escape_atom(a)
{
    chars = a.split('');
    var result = "";
    for (var i = 0; i < chars.length; i++)
    {
        if (chars[i] == "'")
            result += "\\'";
        else
            result += chars[i];       
    }
    return result;
}

function quote_atom(a)
{
    if (a.charAt(0) >= "A" && a.charAt(0) <= "Z")
        return "'" + escape_atom(a) + "'";
    chars = a.split('');
    if (is_punctuation(chars[0]))
    {
        for (var i = 0; i < chars.length; i++)
        {
            if (!is_punctuation(chars[i]))
                return "'" + escape_atom(a) + "'";
        }
    }
    else
    {
        for (var i = 0; i < chars.length; i++)
        {
            if (is_punctuation(chars[i]) || chars[i] == ' ')
                return "'" + escape_atom(a) + "'";
        }
    }
    return a;
}

function is_operator(ftor)
{
    ftor = VAL(ftor);
    if (ftable[ftor][1] == 2 && infix_operators[atable[ftable[ftor][0]]] != undefined)
        return true;
    if (ftable[ftor][1] == 1 && prefix_operators[atable[ftable[ftor][0]]] != undefined)
        return true;
    return false;
}


function format_term(value, options)
{
    if (value == undefined)
        abort("Illegal memory access in format_term: " + hex(value) + ". Dumping...");
    value = deref(value);
    switch(TAG(value))
    {
    case TAG_REF:
        if (VAL(value) > HEAP_SIZE)
        {
            if (state.E > state.B)
                lTop = state.E + state.CP.code[state.CP.offset - 1] + 2;
            else
                lTop = state.B + memory[state.B] + 8;
            return "_L" + (lTop - VAL(value));
        }
        else
            return "_G" + VAL(value);
    case TAG_ATM:
        atom = atable[VAL(value)];
        if (atom == undefined)
            abort("No such atom: " + VAL(value));
        if (options.quoted === true)
            return quote_atom(atom);
        return atom;
    case TAG_INT:
        if ((VAL(value) & (1 << (WORD_BITS-1))) == (1 << (WORD_BITS-1)))
            return (VAL(value) - (1 << WORD_BITS)) + "";
        else
            return VAL(value) + "";
        // fall-through
    case TAG_FLT:
        return floats[VAL(value)] + "";
    case TAG_STR:
        var ftor = VAL(memory[VAL(value)]);
        if (options.numbervars === true && ftor == lookup_functor('$VAR', 1) && TAG(memory[VAL(value)+1]) == TAG_INT)
        {
            var index = VAL(memory[VAL(value)+1]);
            var result = String.fromCharCode(65 + (index % 26));
            if (index >= 26)
                result = result + Math.floor(index / 26);
            return result;
        }
        if (!is_operator(ftor) || options.ignore_ops === true)
        {
            // Print in canonical form functor(arg1, arg2, ...)
            var result = format_term(ftable[ftor][0] ^ (TAG_ATM << WORD_BITS), options) + "(";
            for (var i = 0; i < ftable[ftor][1]; i++)
            {
                result += format_term(memory[VAL(value)+1+i], options);
                if (i+1 < ftable[ftor][1])
                    result += ",";
            }
            return result + ")";            
        }
        else
        {
            // Print as an operator
            var fname = atable[ftable[ftor][0]];
            if (ftable[ftor][1] == 2 && infix_operators[fname] != undefined)
            {
                // Infix operator
                var lhs = format_term(memory[VAL(value)+1], options);
                if (is_punctuation(lhs.charAt(lhs.length-1)) && !is_punctuation(fname.charAt(0)))
                    result = lhs + fname;
                else if (!is_punctuation(lhs.charAt(lhs.length-1)) && is_punctuation(fname.charAt(0)))
                    result = lhs + fname;
                else
                {
                    result = lhs + " " + fname;
                }
                var rhs = format_term(memory[VAL(value)+2], options);
                if (is_punctuation(rhs.charAt(0)) && !is_punctuation(fname.charAt(fname.length-1)))
                    return result + rhs;
                else if (!is_punctuation(rhs.charAt(0)) && is_punctuation(fname.charAt(fname.length-1)))
                    return result + rhs;
                else
                    return result + " " + rhs;
            }
            else if (ftable[ftor][1] == 1 && prefix_operators[fname] != undefined)
            {
                // Prefix operator
                var rhs = format_term(memory[VAL(value)+1], options);
                if (is_punctuation(rhs.charAt(0)) && !is_punctuation(fname.charAt(fname.length-1)))
                    return fname + rhs;
                else if (!is_punctuation(rhs.charAt(0)) && is_punctuation(fname.charAt(fname.length-1)))
                    return fname + rhs;
                else
                    return fname + " " + rhs;

            }
        }
    case TAG_LST:
        if (options.ignore_ops)
            return "'.'(" + format_term(memory[VAL(value)], options) + "," + format_term(memory[VAL(value)+1], options) + ")";
        // Otherwise we need to print the list in list-form
        var result = "[";
        var head = memory[VAL(value)];
        var tail = memory[VAL(value)+1];
        while (true)
        {
            result += format_term(head, options);
            if (tail == NIL)
                return result + "]";
            else if (TAG(tail) == TAG_LST)
            {
                head = memory[VAL(tail)];
                tail = memory[VAL(tail)+1];
                result += ",";
            }
            else 
                return result + "|" + format_term(tail, options) + "]";
        }        
    }
}


function expression_to_term(s, varmap, singletons)
{
    if (typeof(s) == "string")
        return lookup_atom(s);
    else if (typeof(s) == "number")
    {
        if (s == ~~s)
        {
            return (s & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
        }
        else
        {
            return lookup_float(s);
        }
    }
    else if (s.variable_name !== undefined)
    {
        if (varmap[s.variable_name] !== undefined)
        {
            result = state.H;            
            memory[state.H] = varmap[s.variable_name];
            state.H++;
        }
        else
        {
            result = alloc_var();
            varmap[s.variable_name] = result;            
        }
        if (singletons[s.variable_name] === undefined)
            singletons[s.variable_name] = 1;
        else
            singletons[s.variable_name]++;
        return result;
    }
    else if (s.list !== undefined)
    {   
        // Special case for [], as usual, since we do not actually allocate any lists!
        if (s.list.length == 0)
            return NIL;

        var result = alloc_var();
        var tail = result;
        var head;
        for (var i = 0; i < s.list.length; i++)
        {
            unify(tail, state.H ^ (TAG_LST << WORD_BITS));
            head = alloc_var();
            tail = alloc_var();
            unify(head, expression_to_term(s.list[i], varmap, singletons));
        }
        unify(tail, expression_to_term(s.tail, varmap, singletons));
        return result;
    }
    else if (s.functor !== undefined)
    {
        var t = (state.H ^ TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor(s.functor, s.args.length);
        // Reserve space for the args
        var var_args = [];
        for (var i = 0; i < s.args.length; i++)
            var_args[i] = alloc_var();
        for (var i = 0; i < s.args.length; i++)
        {
            z = expression_to_term(s.args[i], varmap, singletons);
            unify(z, var_args[i]);
        }
        return t;
    }
    else
        abort("Invalid expression: " + JSON.stringify(s));
}

function peek_token(s, t)
{
    if (s.peek_tokens === undefined || s.peeked_tokens.length == 0 )
    {
        var tt = {};
        if (!read_token(s, tt))
            return false;
        s.peeked_tokens = [tt.value];
    }
    t.value = s.peeked_tokens[0];
    return true;
}

function unread_token(s, t)
{
    if (s.peeked_tokens === undefined)
        s.peeked_tokens = [t];
    else
        s.peeked_tokens.push(t);
}

function read_token(s, t)
{
    if (s.peeked_tokens !== undefined && s.peeked_tokens.length != 0)
    {
        t.value = s.peeked_tokens.pop();
        return true;
    }
    if (!lex(s.stream, t))
        return false;
    return true;
}

function is_char(c)
{
    return ((c >= 'a' && c <= 'z') ||
            (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') ||
            c == '_');
}

var punctuation_array = ['`', '~', '@', '#', '$', '^', '&', '*', '-', '+', '=', '<', '>', '/', '?', ':', ',', '\\', '.'];

function is_punctuation(c)
{
    return punctuation_array.indexOf(c) != -1;
}

// lex(stream, t) returns a single token in t.value and fails if an exception is raised
function lex(s, t)
{
    var token;
    while(true)
    {
        var c = get_raw_char_with_conversion(s);
        if (c == -1)
        {
            t.value = null;
            return true;
        }
        // Consume any whitespace
        if (c == ' ' || c == '\n' || c == '\t')
            continue;        
        else if (c == '%')
        {
            do
            {
                d = get_raw_char_with_conversion(s);
                if (d == -1)
                {
                    t.value = null;
                    return true;
                }
            } while(d != '\n');
            continue;
        }
        else if (c == '/')
        {
            d = peek_raw_char_with_conversion(s);
            if (d == '*')
            {
                // Block comment
                get_raw_char_with_conversion(s);
                while(true)
                {
                    d = get_raw_char_with_conversion(s);
                    if (d == -1)
                        return syntax_error("end of file in block comment");
                    if (d == '*' && get_raw_char_with_conversion(s) == '/')
                        break;
                }
                continue;
            }
            else
            {
                // My mistake, the term actually begins with /. c is still set to the right thing
                break;
            }
        }
        break;
    }    
    if ((c >= 'A' && c <= 'Z') || c == '_')
    {
        token = {variable_name: "" + c};
        // Variable. May contain a-zA-Z0-9_
        while (true)
        {
            c = peek_raw_char_with_conversion(s);
            if (is_char(c))
            {
                token.variable_name += get_raw_char_with_conversion(s);
            }
            else
            {
                t.value = token; 
                return true;
            }
        } 
    }
    else if ((c >= '0' && c <= '9') || (c == '-' && peek_raw_char_with_conversion(s) >= '0' && peek_raw_char_with_conversion(s) <= '9'))
    {
        // Integer. May contain 0-9 only. Floats complicate this a bit
        var negate = false;
        if (c == '-')
        {
            token = '';
            negate = true;
        }
        else
            token = c - '0';
        var decimal_places = 0;
        var seen_decimal = false;
        while (true)
        {            
            c = peek_raw_char_with_conversion(s);       
            if (seen_decimal)
                decimal_places++;
            if ((c >= '0' && c <= '9'))
            {
                token = token * 10 + (get_raw_char_with_conversion(s) - '0');
            }
            else if (c == '.' && !seen_decimal)
            {
                // Fixme: Also must check that the next char is actually a number. Otherwise 'X = 3.' will confuse things somewhat.
                seen_decimal = true;
                get_raw_char_with_conversion(s);
                continue;
            }
            else if (is_char(c))
                return syntax_error("illegal number" + token + ": " + c);
            else
            {
                if (seen_decimal)
                {
                    for (var i = 1; i < decimal_places; i++)
                        token = token / 10;
                }
                t.value = negate?(-token):token;
                return true;
            }
        }
    }
    else 
    {
        // Either:
        // 1) a term
        // 2) an atom (which is a term with no arguments) 
        // 3) An operator
        // In all cases, first we have to read an atom
        var buffer = "";
        var state = 0;
        if (c == '\'')
        {
            // Easy. The atom is quoted!
            while(true)
            {
                c = get_raw_char_with_conversion(s);
                if (c == '\\')
                    state = (state + 1) % 2;
                if (c == -1)
                    return syntax_error("end of file in atom");
                if (c == '\'' && state == 0)
                    break;
                buffer += c;
            }
            
        }
        else // Not so simple. Have to read an atom using rules, which are actually available only for a fee from ISO...
        {
            buffer += c;
            // An unquoted atom may contain either all punctuation or all A-Za-z0-9_. There are probably more complicated rules, but this will do
            char_atom = is_char(c);
            punctuation_atom = is_punctuation(c);
            while (true)
            {                
                c = peek_raw_char_with_conversion(s);                
                if (c == -1)
                    break;
                if (char_atom && is_char(c))
                    buffer += get_raw_char_with_conversion(s);
                else if (punctuation_atom && is_punctuation(c))
                    buffer += get_raw_char_with_conversion(s);
                else
                    break;
            }            
        }
        t.value=buffer;
        return true;
    }
}

// This is one of the more ridiculous things in the ISO standard
var char_conversion_override = {};
function predicate_char_conversion(a, b)
{
    if (TAG(a) != TAG_ATM)
        return type_error("atom", a);
    if (TAG(b) != TAG_ATM)
        return type_error("atom", b);
    char_conversion_override[atable[VAL(a)]] = atable[VAL(b)];
    return true;
}

function predicate_current_char_conversion(a, b)
{
    if (TAG(a) == TAG_ATM)
    {
        var aname = atable[VAL(a)];
        if (char_conversion_override[aname] === undefined)
            return unify(a, b);
        else
            return unify(lookup_atom(char_conversion_override[aname]), b);
    }
    else if (TAG(b) == TAG_ATM)
    {
        var bname = btable[VAL(b)];
        var keys = Object.keys(char_conversion_override);
        for (var i = 0; i < keys.length; i++)
        {
            if (char_conversion_override[keys[i]] == bname)
                return unify(lookup_atom(keys[i]), a);
        }
        return unify(a,b);
    }
    if (TAG(a) == TAG_REF && TAG(b) == TAG_REF)
    {
        if (state.foreign_retry)
        {
            index = state.foreign_value + 1;         
        }
        else
        {
            create_choicepoint();
            index = 0;
        }
        update_choicepoint_data(index);        
        aname = String.fromCharCode(index);
        unify(a, lookup_atom(aname));
        if (char_conversion_override[aname] === undefined)
            return unify(a, b);
        else
            return unify(lookup_atom(char_conversion_override[aname]), b);

    }
    else
        return type_error(a);
}

function get_raw_char_with_conversion(s)
{
    if (!prolog_flag_values['char_conversion'])
        return get_raw_char(s);    
    var t = get_raw_char(s);
    var tt = char_conversion_override[t];
    if (tt === undefined)
        return t;
    else
        return tt;
}

function peek_raw_char_with_conversion(s)
{
    if (!prolog_flag_values['char_conversion'])
        return peek_raw_char(s);    
    var t = peek_raw_char(s);
    var tt = char_conversion_override[t];
    if (tt === undefined)
        return t;
    else
        return tt;
}


function parser_test()
{
    //do_parser_test("test(1,1).\ntest(1:-1).\ntest:- test, test.\ntest((1,1)).");
    //do_parser_test("foo:- a, b, c.");
    do_parser_test("foo([a|b]).");
}

function parser_test_read(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = stream.data.shift();
            if (t === undefined)
            {                
                return records_read;
            }
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

function do_parser_test(input_string)
{
    s = {peeked_token: undefined,
         stream: new_stream(parser_test_read,
                            null,
                            null,
                            null,
                            null,
                            toByteArray(input_string))};
    state = {H:0};
    while(true)
    {        
        var e = {};
        if (!read_expression(s, Infinity, false, false, e))
        {
            debug("Failed to parse");
            return false;
        }
        e = e.value;
        if (e.end_of_file == true)
            break;
        debug("Read expression: " + expression_to_string(e));
        
        var p = {};
        if (!read_token(s, p))
        {
            debug("Failed to parse");
            return false;
        }
        p = p.value;
        if (p == ".")
        {
        }
        else
        {
            debug("Error: Expression terminated with >" + p + "<");
        }
        if (e.end_of_file !== undefined)
            break;
    }
}

function expression_to_string(s)
{
    if (typeof(s) == "string")
        return s;
    if (typeof(s) == "number")
        return s;
    if (s.variable_name !== undefined)
        return "_" + s.variable_name;
    if (s.list !== undefined)
    {
        t = "[";
        for (var i = 0; i < s.list.length; i++)
        {
            if (i+1 < s.list.length)
                t += expression_to_string(s.list[i]) + ", ";
            else
            {
                t += expression_to_string(s.list[i]) 
                if (s.tail == "[]")
                    t += "]";
                else
                    t += "|" + expression_to_string(s.tail) + "]";
            }
        }
        return t;
    }
    if (s.functor !== undefined)
    {
        t = "" + s.functor + "(";
        for (var i = 0; i < s.args.length; i++)
        {
            if (i+1 < s.args.length)
            {
                t += expression_to_string(s.args[i]) + ", ";
            }
            else
                t += expression_to_string(s.args[i]) + ")";
        }
        return t;
    }
}


function atom_to_term(atom, term, bindings)
{
    var stream = new_stream(read_atom, null, null, null, null, {data:toByteArray(atable[VAL(atom)]), ptr:0});
    var context = {stream:stream, peeked_token: undefined};
    var expression = {};
    if (!read_expression(context, Infinity, false, false, expression))
        return false;
    expression = expression.value;
    b = {};
    t1 = expression_to_term(expression, b, {});
    arglist = [];
    keys = Object.keys(b);
    for (var i = 0 ; i < keys.length; i++)
        arglist.push({functor:"=", args:[keys[i], {variable_name:keys[i]}]});
    t2 = expression_to_term({list:arglist, tail:{list: []}}, b, {});
    return unify(term, t1) && unify(bindings, t2);
}

function read_atom(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    var info = stream.data;
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = info.data[info.ptr++];            
            if (t === undefined)
                return records_read;
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

// File record.js
/* Need to implement recorda/3, recorded/3 and erase/1 */
var database_ptr = 0;
var database_references = {};
var databases = {};

/* 
   Because we don't have access to pointers in Javascript, this is quite hard to do efficiently. It's quite hard to do at all!
   database_references contains a key-value pair with uniquely generated integer keys. The key is returned as a clause reference.
   The database_reference:value is an object containing two values: Array and Index.
   Array is a key into the databases object. The database:value is an array. Index is the index into that array of the actual value
   stored in the clause reference.
   Eventually I will move the code into databases[0]
*/

function recorda(key, term, ref)
{
    // Get the database associated with key. 
    var d = databases[key];
    var i = 0;
    if (d === undefined)
    {
        // No such database yet. Create one, and store it in databases
        databases[key] = {data:{},
                          keys:new Array(),
                          ptr: 0};
        d = databases[key];
    }
    else
    {
        i = d.ptr;
    }
    // Now store the term in d at i
    d.data[i] = {value: record_term(term),
                 ref: database_ptr};
    // And finally, store the key in the keys arrays, putting it at the front
    d.keys.unshift(i);

    
    d.ptr++;
    // Next, save the clause reference in database_references
    database_references[database_ptr] = {array: key,
                                         index: i};
    // And now we can unify it with ref
    var result = unify(ref, database_ptr ^ (TAG_INT << WORD_BITS));
    // And increment it
    database_ptr++;
    return result;
}


function recordz(key, term, ref)
{
    // Get the database associated with key. 
    var d = databases[key];
    var i = 1;
    if (d === undefined)
    {
        // No such database yet. Create one, and store it in databases
        databases[key] = {data:{},
                          keys:new Array(),
                          ptr: 0};
        d = databases[key];
    }
    else
    {
        i = d.ptr;
    }
    // Now store the term in d at i
    d.data[i] = {value: record_term(term),
                 ref: database_ptr};
    // And finally, store the key in the keys arrays, putting it at the front
    d.keys.push(i);

    
    databases[key].ptr++;
    // Next, save the clause reference in database_references
    database_references[database_ptr] = {array: key,
                                         index: i};
    // And now we can unify it with ref
    var result = unify(ref, database_ptr ^ (TAG_INT << WORD_BITS));
    // And increment it
    database_ptr++;
    return result;
}

function recorded(key, term, ref)
{
    // Ok, first find the database
    var d = databases[key];
    // Check if there is anything recorded. If not, fail.
    if (d === undefined)
    {
        return false; 
    }
    // Ok, now we can get the actual array
    var data = d.data;
    // We need the first actual key. This may not be [0] if something has been erased
    var index = d.keys[0];
    var result = unify(recall_term(d.data[index].value, {}), term) && unify(d.data[index].ref ^ (TAG_INT << WORD_BITS), ref);
    return result;
}

function erase(ref)
{
    // First find the array
    var dr = database_references[VAL(ref)];
    if (dr === undefined)
        return false;
    var d = databases[dr.array];
    // Now set to undefined
    delete d.data[dr.index];
    // Now we must also delete the keys entry. This requires a search, unfortunately since there is no way to keep track of indices if we allow unshifting
    for (i = 0; i < d.keys.length; i++)
    {
        if (d.keys[i] == dr.index)
        {
            d.keys.splice(i, 1);
            break;
        }
    }

    return true;
}

// record_term returns a new object which is a javascript representation of the term
function record_term(t)
{
    t = deref(t);
    switch(TAG(t))
    {
    case TAG_REF:
        return {type: TAG_REF,
                key: VAL(t)};
    case TAG_ATM:
        return {type: TAG_ATM,
                value: atable[VAL(t)]};
    case TAG_FLT:
        return {type: TAG_FLT,
                value: floats[VAL(t)]};
    case TAG_INT:
        return {type: TAG_INT,
                value: VAL(t)};
    case TAG_LST:
        var value = [];
        var list = {type: TAG_LST,
                    value: value};
        while (TAG(t) == TAG_LST)
        {
            value.push(record_term(VAL(t)));
            t = memory[VAL(t)+1];
        }
        list.tail = record_term(t);
        return list;
    case TAG_STR:
        var ftor = ftable[VAL(memory[VAL(t)])];
        var args = [];
        var result = {type: TAG_STR,
                      name: atable[ftor[0]],
                      args: args};        
        for (var i = 0; i < ftor[1]; i++)
        {
            args.push(record_term(memory[VAL(t)+1+i]));
        }       
        return result;
    }
}

function recall_term(e, varmap)
{
    // return a reference to an equivalent WAM term to the expression e
    switch(e.type)
    {
    case TAG_REF:
        var result;
        if (varmap[e.key] !== undefined)
        {
            result = state.H;            
            memory[state.H] = varmap[e.key];
            state.H++;
        }
        else
        {
            result = alloc_var();
            varmap[e.key] = result;            
        }
        return result;
    case TAG_ATM:
        return lookup_atom(e.value);
    case TAG_FLT:
        return lookup_float(e.value);
    case TAG_INT:
        return e.value ^ (TAG_INT << WORD_BITS);
    case TAG_LST:
        var result = alloc_var();
        var tail = result;
        var head;
        for (var i = 0; i < e.value.length; i++)
        {
            unify(tail, state.H ^ (TAG_LST << WORD_BITS));
            head = alloc_var();
            tail = alloc_var();
            unify(head, recall_term(e.value[i], varmap));
        }
        unify(tail, recall_term(e.tail, varmap));
        return result;    
    case TAG_STR:
        var t = (state.H ^ TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor(e.name, e.args.length);
        // Reserve space for the args
        var var_args = [];
        for (var i = 0; i < e.args.length; i++)
            var_args[i] = alloc_var();
        for (var i = 0; i < e.args.length; i++)
        {
            z = recall_term(e.args[i], varmap);
            unify(z, var_args[i]);
        }
        return t;
    default:
        abort("invalid term type: " + JSON.stringify(e));
    }
}
// File fli.js
/* Not implemented:
   All the nondet foreign stuff. That is supported, but not using the SWI-Prolog interface
   Strings
   Floats
   Pointers
   PL_get_chars
   PL_predicate_info
   PL_copy_term_ref
   PL_reset_term_refs
*/

function PL_new_term_ref()
{
    // FIXME: Should this go on the heap or the stack?
    return alloc_var();
}

function PL_new_term_refs(n)
{
    var first = alloc_var();
    for (i = 0; i < n-1; i++)
        alloc_var();
        
}

function PL_succeed()
{
    return true;
}

function PL_fail()
{
    return true;
}

function PL_new_atom(chars)
{
    return lookup_atom(chars);
}

function PL_atom_chars(atom)
{
    return atable[VAL(atom)];
}

function PL_new_functor(name, arity)
{
    return lookup_functor(atable[name], arity);
}

function PL_functor_name(ftor)
{
    return ftable[VAL(ftor)][0];
}

function PL_functor_arity(ftor)
{
    return ftable[VAL(ftor)][1];
}

function PL_term_type(term)
{
    return TAG(term);
}

function PL_is_variable(term)
{
    return TAG(term) == TAG_REF;
}

function PL_is_atom(term)
{
    return TAG(term) == TAG_ATM;
}

function PL_is_integer(term)
{
    return TAG(term) == TAG_INT;
}

function PL_is_compound(term)
{
    return TAG(term) == TAG_STR;
}

function PL_is_functor(term, ftor)
{
    return TAG(term) == TAG_STR && memory[VAL(term)] == ftor;
}

function PL_is_list(term)
{
    return TAG(term) == TAG_LST;
}

function PL_is_atomic(term)
{
    return TAG(term) != TAG_STR && TAG(term) != TAG_REF;
}

function PL_is_number(term)
{
    return TAG(term) == TAG_INT; // At the moment
}

function PL_get_atom(term)
{
    if (TAG(term) == TAG_ATM)
        return atom;
    throw("type_error: atom");
}

function PL_get_atom_chars(term)
{
    if (TAG(term) == TAG_ATOM)
        return atable[VAL(term)];
    throw("type_error: atom");
}

function PL_get_integer(term)
{
    if (TAG(term) == TAG_INT)
        return VAL(term);
    throw("type_error: integer");
}

function PL_get_functor(term)
{
    if (TAG(term) == TAG_STR)
        return memory[VAL(term)];
    throw("type_error: term");
}

function PL_get_arg(index, term)
{
    if (index < 1)
        throw("domain_error: term arity");
    if (TAG(term) == TAG_STR)
    {
        if (index > ftable[VAL(memory[VAL(term)])][1])  // Check arity is OK
            throw("type_error: term arity");
        return memory[VAL(term) + index];
    }
    throw("type_error: term");
}

// Returns an object with head and tail keys
function PL_get_list(list)
{
    if (TAG(list) == TAG_LST)
        return {head: memory[VAL(list)],
                tail: memory[VAL(list)+1]};
    return null;
}

function PL_get_head(list)
{
    if (TAG(list) == TAG_LST)
        return memory[VAL(list)];
    return null;
}

function PL_get_tail(list)
{
    if (TAG(list) == TAG_LST)
        return memory[VAL(list)+1];
    return null;
}

function PL_get_nil()
{
    return NIL;
}

function PL_put_variable()
{
    return alloc_var();
}

function PL_put_atom(atom)
{
    return atom;
}

function PL_put_atom_chars(chars)
{
    return lookup_atom(chars);
}

function PL_put_integer(integer)
{
    return integer ^ (TAG_INT << WORD_BITS);
}

function PL_put_functor(term, ftor)
{
    var r = alloc_structure(ftor);
    for (i = 0; i < ftable[VAL(ftor)][1]; i++)
        alloc_var();
}

function PL_put_list()
{
    var r = alloc_list();
    alloc_var();
    alloc_var();
}

function PL_put_nil()
{
    return NIL;
}

function PL_cons_functor(ftor)
{
    if (state.H + arguments.length + 1 >= HEAP_SIZE)
        return false; // Not enough heap
    var r = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    for (i = 1; i < arguments.length; i++)
        memory[state.H++] = arguments[i];
}

function PL_cons_list(head, tail)
{
    if (state.H +2 >= HEAP_SIZE)
        return false;
    var result = state.H ^ (TAG_LST << WORD_BITS);
    memory[state.H++] = head;
    memory[state.H++] = tail;
    return result;
}

function PL_unify_integer(term, integer)
{
    return unify(term, integer ^ (TAG_INT << WORD_BITS));
}

function PL_unify_atom_chars(term, chars)
{
    return unify(term, lookup_atom(string));
}

function PL_unify(t1, t2)
{
    return unify(t1, t2);
}

function PL_unify_atom(term, atom)
{
    return unify(term, atom);
}

function PL_unify_nil(term)
{
    return unify(term, NIL);
}

function PL_unify_arg(index, term, arg)
{
    return unify(memory[VAL(term) + 1 + index], arg);
}

function PL_unify_list(list, head, tail)
{
    return (TAG(list) == TAG_LST) && unify(memory[VAL(list)], head) && unify(memory[VAL(list) + 1], tail);            
}

function PL_pred(ftor, module)
{
    if (predicates[ftor] === undefined)
        throw("Undefined predicate");
    return ftor;
}

function PL_predicate(name, arity, module)
{
    return PL_pred(lookup_functor(name, arity), module);
}

function PL_open_query(module, debug, predicate, args)
{
    initialize();
    allocate_first_frame();
    state.P = predicates[predicate];
    for (i = 0; i < ftable[predicate][1]; i++)
        register[i] = args[i];
    return {fresh:true};
}

function PL_next_solution(qid)
{    
    if (!qid.fresh)
        backtrack();
    qid.fresh = false;
    return wam();
}

function PL_call(term, module)
{
    ftor = VAL(memory[VAL(term)]);
    initialize();
    allocate_first_frame();
    state.P = predicates[ftor];
    for (i = 0; i < ftable[ftor][1]; i++)
        register[i] = memory[VAL(term) + 1 + i];
    return wam();    
}

function PL_cut_query(qid)
{
    // This is not implemented
}

function PL_close_query(qid)
{
    // This is not implemented either
}


function PL_call_predicate(module, debug, predicate, args)
{
    var qid = PL_open_query(module, debug, predicate, args);
    var result = PL_next_solution(qid);
    PL_cut_query(qud);
    return result;
}
// File stream.js
var current_input = null;
var current_output = 0;
// FIXME: Ignores size and count!
function stdout_write(stream, size, count, buffer)
{
    var str = fromByteArray(buffer);
    stdout(str);
    return size*count;
}

function predicate_set_input(stream)
{
    var s = {};
    if (!get_stream_fd(stream, s))
        return false;
    current_input = s.value;
    return true;
}

function predicate_set_output(stream)
{
    var s = {};
    if (!get_stream_fd(stream, s))
        return false;
    current_output = s.value;
    return true;
}

function predicate_current_input(stream)
{   var ftor = lookup_functor('$stream', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = current_input ^ (TAG_INT << WORD_BITS);
    return unify(stream, ref);
}

function predicate_current_output(stream)
{   var ftor = lookup_functor('$stream', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = current_output ^ (TAG_INT << WORD_BITS);
    return unify(stream, ref);
}

function predicate_get_char(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, lookup_atom(_get_char(s.value)));
}

function predicate_get_code(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, (_get_code(s.value) & ((1 << (WORD_BITS-1))-1)) ^ (TAG_INT << WORD_BITS));
}

function predicate_get_byte(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, (getb(s.value) & ((1 << (WORD_BITS-1))-1)) ^ (TAG_INT << WORD_BITS));
}

function predicate_peek_char(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, lookup_atom(peek_char(s.value)));
}

function predicate_peek_code(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, _peek_code(s.value) ^ (TAG_INT << WORD_BITS));
}

function predicate_peek_byte(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return unify(c, (peekb(s.value) & ((1 << (WORD_BITS-1))-1)) ^ (TAG_INT << WORD_BITS));
}

function predicate_put_char(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return putch(s.value, atable[VAL(c)]);
}

function predicate_put_code(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return putch(s.value, VAL(c));
}

function predicate_put_byte(stream, c)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return putb(s.value, VAL(c));
}

function predicate_flush_output(stream)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    if (s.value.write != null)
    {
        return s.value.buffer_size == s.value.write(s.value, 1, s.value.buffer_size, s.value.buffer);
    }
    return permission_error("write", "stream", stream);
}

function predicate_at_end_of_stream(stream)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    return (peekch(s.value) != -1);
}

function predicate_set_stream_position(s, position)
{
    var stream = {};
    if (!get_stream(s, stream))
        return false;
    stream = stream.value;
    if (stream.seek == null)
        return permission_error("seek", "stream", s);
    return stream.seek(stream, VAL(position));
}

/* Actual stream IO */
var streams = [new_stream(null, stdout_write, null, null, null, "")];
function predicate_close(stream, options)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    s = s.value;
    if (s.write != null)
    {
        // Flush output
        // FIXME: If flush fails, then what?
        s.write(s, 1, s.buffer_size, s.buffer);
    }
    if (s.close != null)
    {        
        // FIXME: Ignore s.close(s) if options contains force(true)
        return s.close(s);
    }
    // FIXME: Should be an error
    return false;
}

function get_stream(term, ref)
{
    var fd = {};
    if (!get_stream_fd(term, fd))
        return false;
    ref.value = streams[fd.value];
    return true;
}

function get_stream_fd(term, s)
{
    if (TAG(term) != TAG_STR)
        return type_error("stream", term);
    ftor = VAL(memory[VAL(term)]);
    if (atable[ftable[ftor][0]] == "$stream" && ftable[ftor][1] == 1)
    {
        s.value = VAL(memory[VAL(term)+1]);
        return true;
    }
    return type_error("stream", term);
}

// Streams must all have a buffer to support peeking.
// If the buffer is empty, then fill it via read()
var STREAM_BUFFER_SIZE = 256;

function new_stream(read, write, seek, close, tell, user_data)
{
    return {read: read,
            write: write,
            seek: seek,
            close: close,
            tell: tell,
            data: user_data,
            buffer: [],
            buffer_size: 0};
}

function _get_char(s)
{
    var t = getch(s);
    if (t == -1)
        return "end_of_file";
    else
        return String.fromCharCode(t);
}

function get_raw_char(s)
{
    var t = getch(s);
    if (t == -1)
        return -1;
    else
        return String.fromCharCode(t);
}

function peek_raw_char(s)
{
    var t = peekch(s);
    if (t == -1)
        return -1;
    else
        return String.fromCharCode(t);
}


function _peek_char(s)
{
    var t = peekch(s);
    if (t == -1)
        return "end_of_file";
    else
        return String.fromCharCode(t);
}

function _get_code(s)
{
    return getch(s);
}

function _peek_code(s)
{
    return peekch(s);
}
// See getch for an explanation of what is going on here
function peekch(s)
{
    var b = peekb(s);
    var ch;
    if (b == -1)
        return -1;
    // ASCII
    if (b <= 0x7F)
        return b;
    ch = 0; 
    var mask = 0x20;
    var i = 0;
    for (var mask = 0x20; mask != 0; mask >>=1 )
    {        
        var next = s.buffer[i+1];
        if (next == undefined)
        {
            // This is a problem. We need to buffer more data! But we must also not lose the existing buffer since we are peeking.
            abort("Unicode break in peekch. This is a bug");
        }
        if (next == -1)
            return -1;
        ch = (ch << 6) ^ (next & 0x3f);
        if ((b & mask) == 0)
            break;
        i++;
    }
    ch ^= (b & (0xff >> (i+3))) << (6*(i+1));
    return ch; 
}

function getch(s)
{
    var b = getb(s);
    var ch;
    if (b == -1)
        return -1;
    // ASCII
    if (b <= 0x7F)
        return b;
    ch = 0; 
    // Otherwise we have to crunch the numbers
    var mask = 0x20;
    var i = 0;
    // The first byte has leading bits 1, then a 1 for every additional byte we need followed by a 0
    // After the 0 is the top 1-5 bits of the final character. This makes it quite confusing.
    for (var mask = 0x20; mask != 0; mask >>=1 )
    {        
        var next = getb(s);
        if (next == -1)
            return -1;
        ch = (ch << 6) ^ (next & 0x3f);
        if ((b & mask) == 0)
            break;
        i++;
    }
    ch ^= (b & (0xff >> (i+3))) << (6*(i+1));
    return ch;        
}

function putch(s, c)
{
    if (s.buffer_size < 0)
        return io_error("write");
    s.buffer.push(c);
    s.buffer_size++;    
    return true;
}


function putb(s, c)
{
    if (s.buffer_size < 0)
        return io_error("write");
    s.buffer.push(c);
    s.buffer_size++;    
    return true;
}

function getb(s)
{
    if (s.buffer_size == 0)
    {
        s.buffer_size = s.read(s, 1, STREAM_BUFFER_SIZE, s.buffer);
    }
    if (s.buffer_size < 0)
        return s.buffer_size;
    // FIXME: Can this STILL be 0?
    if (s.buffer_size == 0)
        return -1;
    // At this point the buffer has some data in it
    s.buffer_size--;
    return s.buffer.shift();
}

function peekb(s)
{
    if (s.buffer_size == 0)
    {
        s.buffer_size = s.read(s, 1, STREAM_BUFFER_SIZE, s.buffer);
    }
    if (s.buffer_size < 0)
        return s.buffer_size;
    // FIXME: Can this STILL be 0?
    if (s.buffer_size == 0)
        return -1;
    // At this point the buffer has some data in it
    return s.buffer[0];
}

function get_stream_position(stream, property)
{
    if (stream.tell != null)
    {
        var p = stream.tell(stream) - stream.buffer.length;
        var ftor = lookup_functor('position', 1);
        var ref = alloc_structure(ftor);
        memory[state.H++] = p ^ (TAG_INT << WORD_BITS);
        return unify(ref, property);
    }
    return false;
}

var stream_properties = [get_stream_position];

function predicate_stream_property(stream, property)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    stream = s.value;
    var index = 0;
    if (state.foreign_retry)
    {
        index = state.foreign_value+1;
    }
    else
    {
        create_choicepoint();        
    }
    update_choicepoint_data(index);
    
    if (index >= stream_properties.length)
    {
        destroy_choicepoint();
        return false;
    }    
    return stream_properties[index](stream, property)
}

function predicate_current_stream(stream)
{
    var index = 0;
    if (state.foreign_retry)
    {
        index = state.foreign_value+1;
    }
    else
    {
        create_choicepoint();        
    }
    while (streams[index] === undefined)
    {
        if (index >= streams.length)
        {
            destroy_choicepoint();
            return false;
        }    
        index++;
    }
    update_choicepoint_data(index);
    var ftor = lookup_functor('$stream', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(stream, ref);   
}
// File gc.js
function predicate_gc()
{
    debug("Before GC, heap is " + state.H);
    // WARNING: This assumes ONLY predicate_gc will mark things!
    total_marked = 0;

    // debugging only
/*
    var before = [];
    var e = state.E;
    var envsize = state.CP.code[state.CP.offset - 1];
    while (e != HEAP_SIZE)
    {
        for (var i = 0; i < envsize; i++)
        {
            before.push(record_term(memory[e+2 + i]));
        }
        var envcp = memory[e+1];
        envsize = envcp.code[envcp.offset-1];
        e = memory[e];
    }
*/
//    check_stacks(false);
    mark();
//    check_stacks(true);    
    push_registers();
    sweep_trail();
    sweep_stack(); 


    compact();
    pop_registers();
    state.H = total_marked;
    debug("After GC, heap is " + state.H);    

//    check_stacks(false);
/*
    var after = [];
    var e = state.E;
    var envsize = state.CP.code[state.CP.offset - 1];
    while (e != HEAP_SIZE)
    {
        for (var i = 0; i < envsize; i++)
        {
            after.push(record_term(memory[e+2 + i]));
        }
        var envcp = memory[e+1];
        envsize = envcp.code[envcp.offset-1];
        e = memory[e];
    }
*/
    if (total_marked != 0)
    {
    }
/*
    while (before.length != 0)
    {
        var a = before.pop();
        var b = after.pop();
        at = recall_term(a, {});
        bt = recall_term(b, {});
        if (!predicate_unify(at, bt))
        {
            debug("Error: Terms in environment changed during GC!");
            debug("at = " + term_to_string(at));
            debug("bt = " + term_to_string(bt));
            abort("false");
        }
    }
*/

    return true;
}

function push_registers()
{
    for (var i = 0; i < state.num_of_args; i++)
    {
        memory[state.TR++] = register[i];
    }
}

function pop_registers()
{
    for (var i = state.num_of_args-1; i >= 0; i--)
    {
        register[i] = memory[--state.TR];
    }
}

function sweep_trail()
{
    for (var current = state.TR-1; current >= HEAP_SIZE + STACK_SIZE; current--)
    {
        if (IS_HEAP_PTR(memory[current]))
        {
            into_relocation_chain(VAL(memory[current]), current);
        }
        else
        {
        }
    }
}

function sweep_stack()
{
    sweep_environments(state.E, state.CP.code[state.CP.offset - 1]);
    sweep_choicepoints();
}

function sweep_environments(e, envsize)
{
    while (e != HEAP_SIZE)
    {
        // Traversing backwards to ensure we do not stop prematurely
        for (var y = envsize-1; y >= 0; y--)
        {
            if (IS_HEAP_PTR(memory[e+2 + y]))
            {
                if ((memory[e+2 + y] & M_BIT) == 0)
                {
                    // we have already swept this chain
                    return;
                }
                else 
                {
                    memory[e+2 + y] &= ~M_BIT;
                    into_relocation_chain(VAL(memory[e+2+y]), e+2+y);
                }
            }
        }
        var envcp = memory[e+1];
        // work out the size of the previous environment, using the CP pointer saved in THIS environment.
        // This is why we had to pass size in to mark_environments()
        envsize = envcp.code[envcp.offset-1];
        e = memory[e];
    }
}

function sweep_choicepoints()
{
    var b = state.B;
    while (b != 0)
    {
        var cpcp = memory[b + memory[b] + 2];        
        var envsize = cpcp.code[cpcp.offset-1];
        sweep_environments(memory[b + memory[b] + 1], envsize);
        for (var y = 0; y < memory[b]; y++)
        {
            if (IS_HEAP_PTR(memory[b+y+1]))
            {
                memory[b+y+1] &= ~M_BIT;
                into_relocation_chain(VAL(memory[b+y+1]), b+y+1);
            }
        }
        if ((memory[memory[b + memory[b] + 6]] & M_BIT) == 0)
        {
            // The choicepoint has a saved value for H (ie HB) which is not marked
            // Make a fake atom on the heap and change the HB to point to it
            memory[memory[b + memory[b] + 6]] = NIL ^ (M_BIT)
            total_marked++;
        }
        into_relocation_chain(memory[b + memory[b] + 6], b + memory[b] + 6);
        b = memory[b + memory[b] + 3];
    }
}

function mark()
{
    mark_registers();
    mark_environments(state.E, state.CP.code[state.CP.offset - 1]);
    mark_choicepoints();
}

function compact()
{
    var dest;
    var current;
    dest = total_marked - 1; 
    // Upward
    for (current = state.H-1; current >= 0; current--)
    {
        if ((memory[current] & M_BIT) == M_BIT)
        {
            update_relocation_chain(current, dest);
            if (IS_HEAP_PTR(memory[current]))
            {
                if (VAL(memory[current]) < current)
                {
                    into_relocation_chain(VAL(memory[current]), current);
                }
                else if (VAL(memory[current]) == current)
                {
                    memory[current] = (memory[current] & NV_MASK) ^ dest;
                }
            }
            dest--;
        }
    }

    // Downward
    dest = 0;
    for (current = 0; current < state.H; current++)
    {
        if ((memory[current] & M_BIT) == M_BIT)
        {
            update_relocation_chain(current, dest);
            if (IS_HEAP_PTR(memory[current]) && VAL(memory[current]) > current)
            {
                into_relocation_chain(VAL(memory[current]), dest);
                
                memory[dest] = VAL(memory[dest]) ^ (TAG(memory[current]) << WORD_BITS);
            }
            else
            {
                memory[dest] = memory[current];
                // clear the GC flags
                memory[dest] &= ~F_BIT;
            }            
            memory[dest] &= ~M_BIT;
            dest++;
        }
    }
}

function update_relocation_chain(current, dest)
{
    var j;    
    while ((memory[current] & F_BIT) == F_BIT)
    {
        j = VAL(memory[current]);
        memory[current] = VAL(memory[j]) ^ (memory[current] & (NV_MASK ^ F_BIT)) | (memory[j] & F_BIT);
        memory[j] = dest ^ (memory[j] & NV_MASK);
        memory[j] &= ~F_BIT;                
    }
}

function into_relocation_chain(j, current)
{
    memory[current] = VAL(memory[j]) ^ (memory[current] & (NV_MASK ^ F_BIT)) | (memory[j] & F_BIT);
    memory[j] = current ^ (memory[j] & NV_MASK);
    memory[j] |= F_BIT;        
}

function IS_HEAP_PTR(x)
{
    var tag = TAG(x);
    return (tag == TAG_STR || tag == TAG_LST || tag == TAG_REF) && (VAL(x) < HEAP_SIZE);
}

// Mark all the cells reachable from the registers as reachable (ie set their M bits)
function mark_registers()
{
    for (var i = 0; i < state.num_of_args; i++)
    {
        if (IS_HEAP_PTR(register[i]))
        {
            // register refers to the heap. We have to temporarily put this onto the heap since mark_variable
            // expects an address (ie an index into memory[]) and register[i]
            var tmp = state.H;
            if (state.H == HEAP_SIZE)
                abort("Out of heap during GC");
            memory[state.H++] = register[i];
            mark_variable(tmp);
            state.H--; // We can just clean it up now, since mark_variable is not allowed to write to memory[]
        }
    }
}

// Mark all the cells reachable from the environment 'initial'.
// Note that this takes into account LCO: Trimmed cells are ignored.
// If these are actually needed, mark_choicepoints() will find them
function mark_environments(initial, envsize)
{
    var e = initial;
    while (e != HEAP_SIZE)
    {
        // Traversing backwards to ensure we do not stop prematurely
        for (var y = envsize-1; y >= 0; y--)
        {
            if ((memory[e+2 + y] & M_BIT) == M_BIT)
            {
                // we have already done this chain
                return;
            }
            else if (IS_HEAP_PTR(memory[e+2 + y]))
            {
                // Y-register refers to the heap
                mark_variable(e+2 + y);
            }
            else
            {
            }
        }
        var envcp = memory[e+1];
        // work out the size of the previous environment, using the CP pointer saved in THIS environment.
        // This is why we had to pass size in to mark_environments()
        envsize = envcp.code[envcp.offset-1];
        e = memory[e];
    }
}

function mark_choicepoints()
{
    var b = state.B;
    while (b != 0)
    {
        var cpcp = memory[b + memory[b] + 2];
        var envsize = cpcp.code[cpcp.offset-1];
        mark_environments(memory[b + memory[b] + 1], envsize);
        for (var y = 0; y < memory[b]; y++)
        {
            if (IS_HEAP_PTR(memory[b+y+1]))
            {
                // Y-register refers to the heap
                mark_variable(b + y + 1);
            }
        }
        b = memory[b + memory[b] + 3];
    }
}

var total_marked = 0;

// start is an address: That is, an index into memory[]. It is NOT a cell, so it does NOT have a tag!
// Also, it must be the address of something which is a pointer. That is, VAL(memory[start]) must be another index into memory[].
function mark_variable(start)
{
    current = start;
    next = VAL(memory[current]);
    memory[current] |= F_BIT;
    // mark_variable is always called with something which is either not on the heap
    // or not /really/ on the heap, in the case of register values. Therefore, when we count
    // the first thing, we should increment total_marked to 0, not 1.
    total_marked--;

    while(true) // unwrap goto into while loops
    {
        while (true) // forward
        {
            if ((memory[current] & M_BIT) == M_BIT)
                break; // goto backward
            memory[current] |= M_BIT;
            total_marked++;
            switch(TAG(memory[current]))
            {
            case TAG_REF: // Transformation 1
                if ((memory[next] & F_BIT) == F_BIT)
                {
                    break; // goto backward
                }
                // REVERSE(current, next);
                var temp = VAL(memory[next]);
                var tag = TAG(memory[next]);
                memory[next] = (memory[next] & NV_MASK) ^ current;
                current = next;
                next = temp;
                continue; // goto forward
            case TAG_STR: // Transform 2a
            case TAG_LST: // Transform 2b
                if ((memory[next+1] & F_BIT) == F_BIT)
                    break; // goto backward
                // Optimisation: We can skip the structure if we have already marked all its arguments
                // FIXME: Implement

                if (TAG(memory[current]) == TAG_STR)
                {
                    var i;
                    for (i = 0; i < ftable[VAL(memory[next])][1]; i++)
                    {
                        memory[next+1+i] |= F_BIT;
                    }
                    next = next+i;
                }
                else
                {
                    memory[next+1] |= F_BIT;
                    next = next+1;
                }
                //REVERSE(current, next);
                var temp = VAL(memory[next]);
                memory[next] = (memory[next] & NV_MASK) ^ current;
                current = next;
                next = temp;

                continue; // goto forward
            default:
                // All other types: INT, ATM, FLT, etc
                // Transformation 3
                break; // goto backward
            }
            break; // if we get to the end of forward, we must be wanting to go to backward
        }
        while (true) // backward
        {
            if ((memory[current] & F_BIT) != F_BIT)
            {                
                // current is an internal cell
                // Transformation 4
                //UNDO(current, next);
                var temp = VAL(memory[current]);
                var tag = TAG(memory[next]);
                memory[current] = (memory[current] & NV_MASK) ^ next;
                next = current;
                current = temp;
                continue; // goto backward
            }
            // current is the head of a chain
            memory[current] &= ~F_BIT;
            if (current == start)
            {
                // current is the head of the chain we started with. Finished!
                return;
            }
            // Otherwise, current is the head of a subchain
            current--; // Transformation 5
            //ADVANCE(current, next);
            var temp = VAL(memory[current+1]);
            memory[current+1] = (memory[current+1] & NV_MASK) ^ next;
            next = VAL(memory[current]);
            memory[current] = (memory[current] & NV_MASK) ^ temp;
            break; // goto forward
        }
    }
}



function gc_test(d)
{
    debugging = d;
    load_state();
    initialize();
    stdout("Loaded " + Object.keys(predicates).length + " predicates");
    stdout("Loaded " + atable.length + " atoms");
    stdout("Loaded " + ftable.length + " functors");
    stdout("Loaded " + code.length + " bytes of code");
    
    memory[0] = 0x20000088;
    memory[1] = 0x20000071;
    memory[2] = 0x20000072;
    state.H = 3;
    state.CP.code[state.CP.offset - 1] = 1;
    memory[state.E + 2] = 0x8000000;
    mark_variable(state.E+2);

    compact();
}

function dump_heap()
{
    for (var i = 0; i < state.H; i++)
    {
    }
}

function dump_registers()
{
    for (var i = 0; i < state.num_of_args; i++)
    {
    }
}


function predicate_statistics()
{
    stdout("Heap size: " + state.H + "\n");
    return true;
}

function gc_check(t)
{
    if (t & M_BIT)
        abort("GC exception: " + hex(t) + " has M_BIT set");
}

function check_stacks(m)
{
    check_environments(state.E, state.CP.code[state.CP.offset - 1], m);
}

function check_environments(initial, envsize, m)
{
    var e = initial;
    while (e != HEAP_SIZE)
    {
        // Traversing backwards to ensure we do not stop prematurely
        for (var y = 0; y < envsize; y++)
        {            
            if (TAG(memory[e+2+y]) == TAG_STR || 
                TAG(memory[e+2+y]) == TAG_LST)
            {
                check_term(memory[e+2+y], m);
            }
            else 
            {
            }
            // Otherwise we do not need to check it if it is in the environment
        }
        var envcp = memory[e+1];
        // work out the size of the previous environment, using the CP pointer saved in THIS environment.
        // This is why we had to pass size in to mark_environments()
        envsize = envcp.code[envcp.offset-1];
        e = memory[e];
    }
}

function check_term(t, m)
{
    if (!m)
    {
    }
    if ((t & M_BIT) == M_BIT)
    {
        if (!m)
            abort("Term " + hex(t) + " is marked but should not be");
    }
    else if (m)
    {
        abort("Term " + hex(t) + " is not marked but is reachable");
    }
    if ((t & F_BIT) == F_BIT)
    {
        if (!m)
            abort("Term " + hex(t) + " is F but should not be");
    }

    if (TAG(t) == TAG_LST)
    {
        if (VAL(t) > state.H)
            abort("Term " + hex(t) + " exceeds heap: " + state.H);
        check_term(memory[VAL(t)], m);
        check_term(memory[VAL(t)+1], m);
    }
    else if (TAG(t) == TAG_STR)
    {
        if (VAL(t) > state.H)
            abort("Term " + hex(t) + " exceeds heap: " + state.H);        
        if (ftable[VAL(memory[VAL(t)])] == undefined)
            abort("Illegal functor " + VAL(memory[VAL(t)]));
        var arity = ftable[VAL(memory[VAL(t)])][1];
        for (var i = 0; i < arity; i++)
            check_term(memory[VAL(t)+1+i], m);
    }
    // Everything else we assume is OK
}
