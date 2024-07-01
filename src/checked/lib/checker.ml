(* 
HW5
Name - Rudransh Nagar
CWID: 20011878   
*)

open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error "LetRec: Type of recursive function does not match declaration")
  | NewRef(e) ->
    chk_expr e >>= fun ce ->
    return @@ RefType(ce)
  | DeRef(e) ->
    chk_expr e >>= ref_of_refType "deref: " >>= fun ce ->
    return ce
  | SetRef(e1,e2) ->
    chk_expr e1 >>= ref_of_refType "setref: " >>= fun ce1 ->
    chk_expr e2 >>= fun ce2 ->
    if ce1=ce2
    then return @@ UnitType
    else error "setref: incompatible types"
  | BeginEnd([]) -> 
    return @@ UnitType
    (* re-attempt *)
  | BeginEnd(es) ->
    List.fold_left (fun c e -> c >>= fun _ -> chk_expr e) (return @@ UnitType) es

  | EmptyList(t) -> 
    (match t with
    | None -> return @@ ListType(UnitType)
    | Some(tt) -> return @@ ListType(tt))
  | Cons(e1, e2) -> 
    chk_expr e1 >>= fun ce1 ->
    chk_expr e2 >>= list_of_listType "cons: " >>= fun ce2 ->
    if (ce1=ce2)
    then return @@ ListType(ce2)
    else error "cons: type of head and tail do not match"
  | IsEmpty(e) -> 
    chk_expr e >>= fun ce ->
    (match ce with
    | ListType(_) | TreeType(_) -> (return @@ BoolType)
    | _ -> error "isempty: Expected a List or a Tree!")
  | Hd(e) ->
    chk_expr e >>= list_of_listType "hd: " >>= fun ce ->
    return ce
  | Tl(e) ->
    chk_expr e >>= list_of_listType "tl: " >>= fun ce ->
    return @@ ListType(ce)
  | EmptyTree(t) ->
    (match t with
    | None -> return @@ TreeType(UnitType)
    | Some(tt) -> return @@ TreeType(tt)) 
  | Node(de, le, re) ->
    chk_expr de >>= fun cde ->
    chk_expr le >>= tree_of_treeType "node: " >>= fun cle ->
    chk_expr re >>= tree_of_treeType "node: " >>= fun cre ->
    if cde=cle && cle=cre
    then return @@ TreeType(cde)
    else error "node: Incompatible types"
  | CaseT(target,emptycase,id1,id2,id3,nodecase) ->
    chk_expr target >>= tree_of_treeType "caset: ">>= fun ct ->
    chk_expr emptycase >>= fun cs ->
    extend_tenv id1 ct >>+
    extend_tenv id2 (TreeType(ct)) >>+
    extend_tenv id3 (TreeType(ct)) >>+
    chk_expr nodecase >>= fun cs1 ->
    if cs=cs1
    then return cs
    else error "caset: incompatible types"
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



