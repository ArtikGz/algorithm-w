module Set = Set.Make(String)
module Map = Map.Make(String)


type value =
  | VInt of int
  | VBool of bool
  [@@deriving show { with_path = false }]

type expr =
  | EVar of string
  | EValue of value
  | EAbs of { param : string; body : expr }
  | EApp of { func : expr; arg : expr }
  | ELet of { var : string; init : expr; body : expr } 
  [@@deriving show { with_path = false }]

type ttype =
  | TVar of string
  | TInt
  | TBool
  | TAbs of { arg : ttype; body : ttype }
  [@@deriving show { with_path = false }]

type scheme = Scheme of { vars : string list; typ : ttype } [@@deriving show { with_path = false }]

type subst = ttype Map.t
type ctx = scheme Map.t

let rec ftv_ttype ttype = 
  match ttype with
  | TVar var -> Set.singleton var
  | TInt -> Set.empty
  | TBool -> Set.empty
  | TAbs { arg; body } -> 
    let c1 = ftv_ttype arg in
    let c2 = ftv_ttype body in
    Set.union c1 c2

let rec subst_ttype s ttype = 
  match ttype with
  | TVar var -> (
    match Map.find_opt var s with
    | Some t -> t
    | None -> TVar var)
  | TAbs { arg; body } -> TAbs { arg = subst_ttype s arg; body = subst_ttype s body }
  | t -> t

let ftv_scheme (Scheme { vars; typ }) = Set.diff (ftv_ttype typ) (Set.of_list vars)
let subst_scheme s (Scheme { vars; typ }) =
  let remove subst_map variables = List.fold_right Map.remove variables subst_map in
  Scheme { vars; typ = subst_ttype (remove s vars) typ }

let compose_subst s1 s2 = Map.union (fun key t1 t2 -> Some t1) s1 (Map.map (subst_ttype s1) s2)
let ( <> ) = compose_subst

let ftv_ctx ctx = 
  let tem = List.map snd (Map.to_list ctx) in
  List.fold_right (fun scheme acc -> Set.union acc (ftv_scheme scheme)) tem Set.empty

let subst_ctx s tem = Map.map (subst_scheme s) tem

let generalize env typ = 
  let vars = Set.diff (ftv_ttype typ) (ftv_ctx env) in
  (Scheme { vars = Set.to_list vars; typ })

module type UNIFY = sig
  val mgu : ttype -> ttype -> subst
end
module Unify : UNIFY = struct
  let unify_error t1 t2 = Printf.sprintf "Unable to unify %s and %s." (show_ttype t1) (show_ttype t2)
  let hole_error var expected = Printf.sprintf "Found hole %s : %s." var (show_ttype expected) 
  
  let is_hole = function
    | TVar u when String.starts_with ~prefix:"_" u -> true
    | _ -> false 

  let hole_name = function
    | TVar u -> u
    | _ -> failwith "Not a hole."


  let rec mgu t1 t2 =
    let var_bind var t = 
      match t with
      | TVar u when String.equal u var -> Map.empty
      | t when Option.is_some (Set.find_opt var (ftv_ttype t)) -> failwith (unify_error t1 t2)
      | _ -> Map.singleton var t
    in
    if is_hole t2 then failwith (hole_error (hole_name t2) t1) 
    else
      match (t1, t2) with 
      | (TInt, TInt) -> Map.empty
      | (TBool, TBool) -> Map.empty
      | (TVar a, b) -> var_bind a b
      | (a, TVar b) -> var_bind b a
      | (TAbs { arg; body }, TAbs { arg = arg1; body = body1 }) -> 
        let s1 = mgu arg arg1 in
        let s2 = mgu (subst_ttype s1 body) (subst_ttype s1 body1) in
        s1 <> s2
      | (_, _) -> failwith (unify_error t1 t2)
end

module type COUNTER = sig
  val newVar : unit -> ttype
end
module Counter : COUNTER = struct
  let r = ref 0

  let newVar () = 
    let v = !r in
    r := !r + 1;
    TVar (String.concat "" ["t";string_of_int v])
end

let instantiate (Scheme { vars; typ }) =
  let nvars = List.map (fun _ -> Counter.newVar ()) vars in
  let s = Map.of_list (List.combine vars nvars) in
  subst_ttype s typ

(* Γ → expr → SubstMap × ttype *)
let rec infer ctx e =
  let find_var var = 
    match Map.find_opt var ctx with
    | Some t -> t
    | _ -> failwith (Printf.sprintf "Unbound variable %s." var)
  in
  match e with
  | EVar x -> 
      let omega = find_var x in
      let tau = instantiate omega in
      (Map.empty, tau)
  | EValue v -> (match v with
    | VInt _ -> (Map.empty, TInt)
    | VBool _ -> (Map.empty, TBool))
  | EAbs { param; body } ->
    let tau = Counter.newVar () in
    let (s1, tau') = infer (Map.add param (Scheme { vars = []; typ = tau}) ctx) body in
    (s1, subst_ttype s1 (TAbs { arg = tau; body = tau' }))
  | EApp { func; arg } -> 
    let (s0, tau0) = infer ctx func in
    let (s1, tau1) = infer (subst_ctx s0 ctx) arg in
    let tau' = Counter.newVar () in
    let s2 = Unify.mgu (subst_ttype s1 tau0) (TAbs { arg = tau1; body = tau' }) in
    ((s1 <> s0) <> s2, subst_ttype s2 tau')
  | ELet { var; init; body } -> 
    let (s0, tau) = infer ctx init in
    let g = generalize (subst_ctx s0 ctx) tau in
    infer (subst_ctx s0 (Map.add var g ctx)) body

(* code : x -> y -> int *)
let f = EAbs {
    param = "x";
    body = EAbs {
      param = "y";
      body = EVar "_a" (*EValue (VInt 10)*)
    }
  }
let code = 
  EApp {
    func = EApp {
      func = f;
      arg = EValue (VInt 5)
    };
    arg = EValue (VInt 5)
  }
  

let () = 
  try
    let (s, typ) = infer Map.empty code in
    Printf.printf "Original type: %s\n" (show_ttype typ);
    print_endline "Substitutions: ";
    Map.iter (fun k v -> print_endline (Printf.sprintf "Substitution: %s:%s" k (show_ttype v))) s;
    print_endline "Check with test: ";
    Printf.printf "Resulting type: %s\n" (show_ttype (subst_ttype s typ))
  with
  | Failure s -> print_endline s
