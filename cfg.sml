(* Context Free Grammer impl written in Standard ML
 * author: @masquerade0324 *)

datatype symbol = TERM of string
                | NTERM of string

type prod = symbol * symbol list

fun compare (TERM a, TERM b)   = String.compare (a, b)
  | compare (NTERM A, NTERM B) = String.compare (A, B)
  | compare (TERM a, NTERM A)  = GREATER
  | compare (NTERM A, TERM a)  = LESS

(* set structure from smlnj-lib *)
structure Set =
  RedBlackSetFn (
    struct
      type ord_key = symbol
      val compare = compare
    end)

(* map structure from smlnj-lib *)
structure Map =
  RedBlackMapFn (
    struct
      type ord_key = symbol
      val compare = compare
    end)

fun initNullable syms =
  let
    fun init (sym, map) = Map.insert (map, sym, false)
  in
    foldl init Map.empty syms
  end

fun updateNullable nullable (x, ys) =
  let
    val b  = Map.lookup (nullable, x)
    val b' = b orelse List.all (fn y => Map.lookup (nullable, y)) ys
  in
    (Map.insert (nullable, x, b'), b <> b')
  end

fun calcNullable nullable prods =
  let
    fun f (prod, (nl, b)) =
      let
        val (nl', b') = updateNullable nl prod
      in
        (nl', b orelse b')
      end
    val (nullable', isUpdated) = foldl f (nullable, false) prods
  in
    if isUpdated then calcNullable nullable' prods else nullable'
  end

fun initFirst syms =
  let
    fun init (t as TERM a, map)  = Map.insert (map, t, Set.singleton t)
      | init (n as NTERM A, map) = Map.insert (map, n, Set.empty)
  in                                 
    foldl init Map.empty syms
  end

fun updateFirst first nullable (x, ys) =
  let
    fun subRhs []         = []
      | subRhs (sym::rhs) = if Map.lookup (nullable, sym)
                            then sym::subRhs rhs else [sym]
    val ys'   = subRhs ys
    val fstX  = Map.lookup (first, x)
    val fstX' = foldl (fn (y, fstY) =>
                          Set.union (fstY, Map.lookup (first, y))) fstX ys'
  in
    (Map.insert (first, x, fstX'), not (Set.equal (fstX, fstX')))
  end

fun calcFirst first nullable prods =
  let
    fun f (prod, (fst, flg)) =
      let
        val (fst', flg') = updateFirst fst nullable prod
      in
        (fst', flg orelse flg')
      end
    val (first', isUpdated) = foldl f (first, false) prods
  in
    if isUpdated then calcFirst first' nullable prods else first'
  end

fun initFollow syms =
  let
    fun init (sym, map) = Map.insert (map, sym, Set.empty)
  in
    foldl init Map.empty syms
  end

exception Exception

fun updateFollow follow nullable first (x, [])  = (follow, false)
  | updateFollow follow nullable first (x, rhs) =
  let
    fun subRhs []         = []
      | subRhs (sym::rhs) = if Map.lookup (nullable, sym)
                            then sym::subRhs rhs else [sym]
    fun updateFollowY _ [] = raise Exception
      | updateFollowY flwX (y::ys) =
      let
        val flwY  = Map.lookup (follow, y)
        val ys'   = subRhs ys
        val flwY1 = if List.all (fn z => Map.lookup (nullable, z)) ys
                    then Set.union (flwY, flwX) else flwY
        val flwY2 = foldl (fn (y, flwZ) =>
                              Set.union (flwZ, Map.lookup (first, y))) flwY ys'
        val flwY' = Set.union (flwY1,flwY2) 
      in
        ((y, flwY'), not (Set.equal (flwY, flwY')))
      end
    fun apply f []  = raise Exception
      | apply f [z] = [f [z]]
      | apply f zs  = f zs::apply f (tl zs)
    val flwX = Map.lookup (follow, x)
    val lst = apply (updateFollowY flwX) rhs
  in
    foldl (fn (((y, flwY), b), (flw, b')) =>
              (Map.insert (flw, y, flwY), b orelse b')) (follow, false) lst
  end

fun calcFollow follow nullable first prods =
  let
    fun f (prod, (flw, flg)) =
      let
        val (flw', flg') = updateFollow flw nullable first prod
      in
        (flw', flg orelse flg')
      end
    val (follow', isUpdated) = foldl f (follow, false) prods
  in
    if isUpdated then calcFollow follow' nullable first prods else follow'
  end

fun sym2s (TERM a)  = a
  | sym2s (NTERM A) = A

fun syms2s []          = "eps"
  | syms2s [sym]       = sym2s sym
  | syms2s (sym::syms) = sym2s sym ^ " " ^ syms2s syms

fun prod2s ((sym, syms) : prod) = sym2s sym ^ " -> " ^ syms2s syms

fun println s = print (s ^ "\n")

fun printNullable nullable =
  Map.appi (fn (sym, b) =>
               println (sym2s sym ^ " : " ^ Bool.toString b)) nullable

fun printFirst first =
  Map.appi
    (fn (sym, set) =>
        println (sym2s sym ^ " : " ^
                 String.concatWith " " (map sym2s (Set.toList set)))) first

val printFollow = printFirst

(* Example: Expression Grammer
 *   E  -> T E'
 *   E' -> + T E' | eps
 *   T  -> F T'
 *   T' -> * F T' | eps
 *   F  -> ( E ) | id
 *)

(* terminal *)
val plus  = TERM "+"
val times = TERM "*"
val lpar  = TERM "("
val rpar  = TERM ")"
val id    = TERM "id"

(* nonterminal *)
val E  = NTERM "E"
val E' = NTERM "E'"
val T  = NTERM "T"
val T' = NTERM "T'"
val F  = NTERM "F"

(* production *)
val prod1 : prod = (E, [T, E'])
val prod2 : prod = (E', [plus, T, E'])
val prod3 : prod = (E', [])
val prod4 : prod = (T, [F, T'])
val prod5 : prod = (T', [times, F, T'])
val prod6 : prod = (T', [])
val prod7 : prod = (F, [lpar, E, rpar])
val prod8 : prod = (F, [id])

val syms  = [plus, times, lpar, rpar, id, E, E', T, T', F]
val prods = [prod1, prod2, prod3, prod4, prod5, prod6, prod7, prod8]

val nullable = calcNullable (initNullable syms) prods
val first    = calcFirst (initFirst syms) nullable prods
val follow   = calcFollow (initFollow syms) nullable first prods

val () = (println "----- productions -----";
          app (println o prod2s) prods;
          println "";
          println "----- nullable set -----";
          printNullable nullable;
          println "";
          println "----- first set -----";
          printFirst first;
          println "";
          println "----- follow set -----";
          printFollow follow)
