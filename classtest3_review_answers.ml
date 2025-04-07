
type op = Minus | Plus | Times | Lt | Eq
          
type prefix_op = Log | Exp | Not | Negate (* Log and Exp yield the rounded integers *) 

type name = string
  
type tp =
  | Int
  | Bool 
  | Tuple of tp * tp 
  | Maybe of tp

type exp =
  | N of int
  | B of bool
  | Op of exp * op * exp
  | If of exp (*condition*) * exp (*then-branch*) * exp (*else-branch*)
  | Let of name * exp * exp (* let x = e1 in e2 *)
  | Var of name 
      
  | Tup of exp * exp
  | LetFst of name * exp * exp (* let x = fst e1 in e2 *)
  | LetSnd of name * exp * exp (* let x = snd e1 in e2 *)
  | Pre of prefix_op * exp
           
  | Yes of exp  (* yes e : successful computation with value e *)
  | No of tp (* no A : failure to produce a value of type A *)
  | LetYes of name * exp * exp (* let yes x = e1 in e2 : bind x if e1 = yes v *)
  | Try of exp * exp (* try e1 with e2 : fallback to e2 if e1 = no A *)
  (* We can use this to implement safe operations such as a safe log *)
exception TypeError of string
    
let safe_log = If (Op (N 0, Lt, Var "x"), Yes (Pre (Log, Var "x")), No Int)

    (* if 2 + 2 = 5 then true else 17 *)
let ex = If (
    Op (Op (N 2, Plus, N 3), Eq, N 5) (* 2 + 2 = 5 *),
    Op (B true, Eq, B false), (* true * false *)
    N 17 (* 17 *)
  )

let infer_op op (t1 : tp) (t2 : tp) = match op, t1, t2 with
  | (Plus | Minus | Times), Int, Int -> Int
  | Lt, Int, Int -> Bool
  | Eq, Int, Int -> Bool
  | Eq, Bool, Bool -> Bool
  | _ -> raise (TypeError "type mismatch for operator")
  
type ctx = (name * tp) list

let rec infer (ctx : ctx) (e : exp) : tp = match e with
  | N _ -> Int
  | B _ -> Bool
  | If (e, e1, e2) ->
      begin match infer ctx e with
        | Bool ->
            begin match infer ctx e1, infer ctx e2 with
              | t1, t2 when t1 = t2 -> t1
              | _ -> raise (TypeError "if branches must agree")
            end
        | _ -> raise (TypeError "condition must be boolean")
      end
  | Op (e1, op, e2) ->
      infer_op op (infer ctx e1) (infer ctx e2)
  | Var x -> begin match List.assoc_opt x ctx with
      | None -> raise (TypeError "unbound variable")
      | Some t -> t
    end 
  | Let (x, e1, e2) -> (* let x = 2 + 5 in if z < 17 then ... else ... *)
      let t = infer ctx e1 in
      infer ((x, t) :: ctx) e2 
(* Complete the infer function for the new expressions *)
  | Tup (e1, e2) -> Tuple (infer ctx e1, infer ctx e2)
  | LetFst (x, e1, e2) -> begin match infer ctx e1 with
      | Tuple (t, _) -> infer ((x, t) :: ctx) e2
      | _ -> raise (TypeError "LetFst expects a tuple")
    end
  | LetSnd (x, e1, e2) -> begin match infer ctx e1 with
      | Tuple (_, t) -> infer ((x, t) :: ctx) e2
      | _ -> raise (TypeError "LetSnd expects a tuple")
    end
  | Pre (op, e1) -> begin
      match op, infer ctx e1 with
      | (Exp | Log | Negate), Int -> Int
      | Not, Bool -> Bool
      | _ -> raise (TypeError "type mismatch for operator")
    end
  | Yes e -> Maybe (infer ctx e)
  | No t -> Maybe t
  | LetYes (x, e1, e2) -> begin
      match infer ctx e1 with
      | Maybe t -> infer ((x, t) :: ctx) e2
      | _ -> raise (TypeError "LetYes expects maybe type")
    end
  | Try (e1, e2) ->
      match infer ctx e1 with
      | Maybe t -> if t = infer ctx e2 then t
          else raise (TypeError "Try branches must agree")
      | _ -> raise (TypeError "Try expects maybe type")
  
                     
exception RuntimeError of string

let do_op (op : op) (v1 : exp) (v2 : exp) = match op, v1, v2 with
  | Plus, N n1, N n2 -> N (n1 + n2)
  | Times, N n1, N n2 -> N (n1 * n2)
  | Minus, N n1, N n2 -> N (n1 - n2)
  | Eq, N n1, N n2 -> B (n1 = n2)
  | Eq, B b1, B b2 -> B (b1 = b2)
  | Lt, N n1, N n2 -> B (n1 < n2)
  | _ -> raise (RuntimeError "bad operation arguments")
           
let do_prefix_op (op : prefix_op) (v1 : exp) = match op, v1 with
  | Exp, N n -> N (int_of_float (exp (float_of_int n)))
  | Log, N n -> N (int_of_float (log (float_of_int n))) 
  | Negate, N n -> N (-n)
  | Not, B b -> B (not b)
  | _ -> raise (RuntimeError "bad operation arguments")

  (* subst (e', x) e = [e'/x]e performs a capture-avoiding substitution of e' for x in e. *)
let rec subst (e', x : exp * name) (e : exp) : exp =
  match e with
  | N _ | B _ -> e
  | Var y -> if y = x then e' else e
  | Op (e1, op, e2) ->
      Op (subst (e', x) e1, op, subst (e', x) e2)
  | If (cond, e1, e2) ->
      If (subst (e', x) cond, subst (e', x) e1, subst (e', x) e2)
  | Let (y, e1, e2) ->
      if y = x then
        Let (y, subst (e', x) e1, e2)
      else if List.mem y (free_vars e') then
        let y' = fresh_name y (free_vars e' @ free_vars e2) in
        let e2' = subst (Var y', y) e2 in
        Let (y', subst (e', x) e1, subst (e', x) e2')
      else
        Let (y, subst (e', x) e1, subst (e', x) e2) 
(* Complete the subst function for the new expressions *) 
  | LetFst (y, e1, e2) -> if y = x then
        LetFst (y, subst (e', x) e1, e2)
      else if List.mem y (free_vars e') then
        let y' = fresh_name y (free_vars e' @ free_vars e2) in
        let e2' = subst (Var y', y) e2 in
        LetFst (y', subst (e', x) e1, subst (e', x) e2')
      else
        LetFst (y, subst (e', x) e1, subst (e', x) e2) 
  | LetSnd (y, e1, e2) -> if y = x then
        LetSnd (y, subst (e', x) e1, e2)
      else if List.mem y (free_vars e') then
        let y' = fresh_name y (free_vars e' @ free_vars e2) in
        let e2' = subst (Var y', y) e2 in
        LetSnd(y', subst (e', x) e1, subst (e', x) e2')
      else
        LetSnd (y, subst (e', x) e1, subst (e', x) e2) 
  | Tup (e1, e2) -> Tup (subst (e', x) e1, subst (e', x) e2)
  | Pre (p, e1) -> Pre (p, subst (e', x) e1)
  | Yes e1 -> Yes (subst (e', x) e1)
  | No _ -> e
  | LetYes (y, e1, e2) ->
      if y = x then
        LetYes (y, subst (e', x) e1, e2)
      else if List.mem y (free_vars e') then
        let y' = fresh_name y (free_vars e' @ free_vars e2) in
        let e2' = subst (Var y', y) e2 in
        LetYes (y', subst (e', x) e1, subst (e', x) e2')
      else
        LetYes (y, subst (e', x) e1, subst (e', x) e2) 
  | Try (e1, e2) -> Try (subst (e', x) e1, subst (e', x) e2)
    

and free_vars (e : exp) : name list =
  match e with
  | N _ | B _ -> []
  | Var x -> [x]
  | Op (e1, _, e2) -> free_vars e1 @ free_vars e2
  | If (c, e1, e2) -> free_vars c @ free_vars e1 @ free_vars e2
  | Let (x, e1, e2) ->
      free_vars e1 @ List.filter (fun v -> v <> x) (free_vars e2) 
(* Complete the free_vars function for the new expressions *) 
  | LetFst (x, e1, e2) | LetSnd (x, e1, e2) -> 
      free_vars e1 @ List.filter (fun v -> v <> x) (free_vars e2) 
  | Tup (e1, e2) -> free_vars e1 @ free_vars e2 
  | Pre (_, e1) -> free_vars e1
  | Yes e1 -> free_vars e1
  | No _ -> []
  | LetYes (x, e1, e2) ->
      free_vars e1 @ List.filter (fun v -> v <> x) (free_vars e2)
  | Try (e1, e2) -> free_vars e1 @ free_vars e2
                      
and fresh_name (base : name) (avoid : name list) : name =
  let rec try_name i =
    let candidate = base ^ string_of_int i in
    if List.mem candidate avoid then try_name (i + 1)
    else candidate
  in try_name 0

let rec eval (e : exp) : exp = match e with
  | N n -> N n
  | B b -> B b
  | Op (e1, op, e2) -> do_op op (eval e1) (eval e2)
  | If (e, e1, e2) ->
      begin match eval e with
        | B b -> if b then eval e1 else eval e2
              (* | NV n -> if n <> 0 then eval e1 else eval e2 *)
        | _ -> raise (RuntimeError "if condition must be boolean")
      end
  | Let (x, e1, e2) ->
      let v = eval e1 in
      eval (subst (v, x) e2) (* [v/x]e2 *)
  | Var _ -> raise (RuntimeError "free variable during evaluation") 
(* Complete the eval function for the new expressions *) 
  | Tup (e1, e2) -> Tup (eval e1, eval e2)
  | LetFst (x, e1, e2) -> begin match eval e1 with
      | Tup (v, _) -> eval (subst (v, x) e2)
      | _ -> raise (RuntimeError "LetFst expects a tuple") 
    end
  | LetSnd (x, e1, e2) -> begin match eval e1 with
      | Tup (_, v) -> eval (subst (v, x) e2)
      | _ -> raise (RuntimeError "LetSnd expects a tuple")
    end
  | Pre (p, e1) -> do_prefix_op p (eval e1)
  | Yes e1 -> Yes (eval e1)
  | No t -> No t
  | LetYes (x, e1, e2) -> begin
      match eval e1 with
      | Yes v -> eval (subst (v, x) e2)
      | No t -> No t
      | _ -> raise (RuntimeError "LetYes expects a maybe value")
    end
  | Try (e1, e2) ->
      begin match eval e1 with
        | Yes v -> v
        | No _ -> eval e2
        | _ -> raise (RuntimeError "Try expects a maybe value")
      end
(* Capture-avoiding substitutions *) 
(* SEE PDF *)
                                             
(* What are the free variables? What are the bound variables? *) 
(* What should each expression evaluate to? *)

let e1 =
  Let ("x", Var "y",
       Let ("y", Var "x",
            Op (Var "x", Plus, Var "y")))

let sub1 = subst (N 1, "y") 
    (subst (N 5, "b")
       (subst (N 3, "a") 
          (subst (Op (Var "a", Plus, Var "b"), "x") e1)))

    (*N 2*)

let e2 =
  Let ("x", N 1,
       Let ("x", N 2,
            Let ("x", N 3,
                 Op (Var "x", Plus, Var "x"))))

let sub2 = subst (Var "z", "x") e2
    
    (*N 6*)

let e3 =
  Let ("y", Var "x",
       If (
         Op (Var "y", Lt, Var "x"),
         Var "x",
         Var "y"))

let sub3 = subst (Let ("x", N 0, Var "x"), "x") e3
    
    (*N 0*) 

let e4 =
  Let ("x", Var "y",
       Let ("y", Var "x",
            Let ("z",
                 Op (Var "x", Plus, Op (Op (Var "x", Plus, Var "y"), Plus, Var "z"))
                , Var "z")))

let sub4 = subst (N 7, "y") (subst (N 2, "z") (subst (N 3, "x") e4 ))
    
    (*N 23*) 
    
let substlog1 = subst (N 3, "x") safe_log
let substlog2 = subst (N -3, "x") safe_log







