type level = int
type name = string

type term =
    | Var of name
    | Universe of level
    | Pi of name * term * term
    | Lam of name * term * term
    | App of term * term
    | Inductive of inductive
    | Constr of int * inductive * term list
    | Ind of inductive * term * term list * term
and inductive = {
    name: string;
    params: (name * term) list;
    level: level;
    constrs: (int * term) list
}


let fresh_var used x =
  let rec fresh n =
      let candidate = x ^ string_of_int n in
      if List.mem candidate used then fresh (n+1) else candidate
  in fresh 0

(* Helper function to get free variables *)
and free_vars t = 
    let rec fv acc = function
        | Var x -> x :: acc
        | Universe _ -> acc
        | Pi (x, a, b) -> fv (List.filter ((<>) x) (fv acc b)) a
        | Lam (x, a, t) -> fv (List.filter ((<>) x) (fv acc t)) a
        | App (t1, t2) -> fv (fv acc t2) t1
        | Inductive i -> 
            List.fold_left (fun acc (_,t) -> fv acc t) acc i.params @
            List.fold_left (fun acc (_,t) -> fv acc t) acc i.constrs
        | Constr (_, _, ts) -> List.fold_left fv acc ts
        | Ind (_, t, ts, r) -> fv (fv (List.fold_left fv acc ts) r) t
    in List.sort_uniq compare (fv [] t)


  
  let rec subst x v t used = match t with
      | Var y when y = x -> v
      | Var y -> Var y
      | Universe l -> Universe l
      | Pi (y, a, b) when y = x -> Pi (y, subst x v a used, b)
      | Pi (y, a, b) -> 
          if List.mem y (free_vars v) then
              let y' = fresh_var used y in
              let b' = subst y (Var y') b (y'::used) in
              Pi (y', subst x v a used, subst x v b' used)
          else Pi (y, subst x v a used, subst x v b used)
      | Lam (y, a, t) when y = x -> Lam (y, subst x v a used, t)
      | Lam (y, a, t) -> 
          if List.mem y (free_vars v) then
              let y' = fresh_var used y in
              let t' = subst y (Var y') t (y'::used) in
              Lam (y', subst x v a used, subst x v t' used)
          else Lam (y, subst x v a used, subst x v t used)
      | App (t1, t2) -> App (subst x v t1 used, subst x v t2 used)
      | Inductive i -> Inductive {i with params = List.map (fun (n,t) -> (n, subst x v t used)) i.params;
                                       constrs = List.map (fun (n,t) -> (n, subst x v t used)) i.constrs}
      | Constr (n, i, ts) -> Constr (n, i, List.map (fun t -> subst x v t used) ts)
      | Ind (i, t, ts, r) -> Ind (i, subst x v t used, List.map (fun t -> subst x v t used) ts, subst x v r used)
  
  let subst x v t = subst x v t (free_vars t)

(* Beta reduction - one step *)
let rec beta_reduce t = match t with
    | App (Lam (x, _, t1), t2) -> subst x t2 t1
    | App (t1, t2) -> 
        let t1' = beta_reduce t1 in
        if t1' != t1 then App (t1', t2)
        else App (t1', beta_reduce t2)
    | Pi (x, a, b) -> Pi (x, beta_reduce a, beta_reduce b)
    | Lam (x, a, t) -> Lam (x, beta_reduce a, beta_reduce t)
    | Inductive i -> Inductive {i with params = List.map (fun (n,t) -> (n, beta_reduce t)) i.params;
                                     constrs = List.map (fun (n,t) -> (n, beta_reduce t)) i.constrs}
    | Constr (n, i, ts) -> Constr (n, i, List.map beta_reduce ts)
    | Ind (i, t, ts, r) -> Ind (i, beta_reduce t, List.map beta_reduce ts, beta_reduce r)
    | Var x -> Var x
    | Universe l -> Universe l

(* Eta reduction - one step *)
let rec eta_reduce t = match t with
    | Lam (x, a, App (t1, Var y)) when y = x && not (List.mem x (free_vars t1)) -> t1
    | Pi (x, a, b) -> Pi (x, eta_reduce a, eta_reduce b)
    | Lam (x, a, t) -> Lam (x, eta_reduce a, eta_reduce t)
    | App (t1, t2) -> App (eta_reduce t1, eta_reduce t2)
    | Inductive i -> Inductive {i with params = List.map (fun (n,t) -> (n, eta_reduce t)) i.params;
                                     constrs = List.map (fun (n,t) -> (n, eta_reduce t)) i.constrs}
    | Constr (n, i, ts) -> Constr (n, i, List.map eta_reduce ts)
    | Ind (i, t, ts, r) -> Ind (i, eta_reduce t, List.map eta_reduce ts, eta_reduce r)
    | Var x -> Var x
    | Universe l -> Universe l
(* Full normalization *)
let rec normalize ?(depth=100) t =
    if depth <= 0 then t  (* Гранична умова: зупинка при великій глибині *)
    else
        let t' = beta_reduce t in
        let t'' = eta_reduce t' in
        if t'' = t then t
        else normalize ~depth:(depth-1) t''

(* Pretty printing *)
let rec string_of_term = function
    | Var n -> n
    | Universe l -> "U" ^ string_of_int l
    | Pi (n, t1, t2) -> "Π(" ^ n ^ ":" ^ string_of_term t1 ^ ")." ^ string_of_term t2
    | Lam (n, a, t) -> "λ(" ^ n ^ ":" ^ string_of_term a ^ ")." ^ string_of_term t
    | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"
    | Inductive i -> "Inductive " ^ i.name
    | Constr (n, _, ts) -> "Constr" ^ string_of_int n ^ "(" ^ String.concat "," (List.map string_of_term ts) ^ ")"
    | Ind (i, t, _, _) -> "Ind(" ^ i.name ^ "," ^ string_of_term t ^ ")"

(* Test examples *)
let test1 = App (Lam ("x", Universe 0, Var "x"), Universe 1)  (* (λx:U0.x) U1 *)
let test2 = Lam ("x", Universe 0, App (Var "f", Var "x"))    (* λx:U0.(f x) *)
let test_loop = App (Lam ("x", Universe 0, App (Var "x", Var "x")), 
    Lam ("x", Universe 0, App (Var "x", Var "x")))
let test_capture = App (Lam ("x", Universe 0, Lam ("y", Universe 0, Var "x")), Var "y")
let test_multi_beta = App (Lam ("x", Universe 0, App (Lam ("y", Universe 0, Var "x"), Var "z")), Var "w")
let test_eta_nested = Lam ("x", Universe 0, App (Lam ("y", Universe 0, Lam ("z", Universe 0, Var "z")), Var "x"))
let test_eta_nested = Lam ("x", Universe 0, App (Var "id", Var "x"))
let test_pi_domain = Pi ("x", App (Lam ("a", Universe 0, Var "a"), Var "b"), App (Lam ("c", Universe 0, Var "c"), Var "x"))
let nat_inductive = {
    name = "Nat";
    params = [];
    level = 0;
    constrs = [
        (0, Var "Nat");  (* 0 : Nat *)
        (1, Pi ("n", Var "Nat", Var "Nat"))  (* S : Nat → Nat *)
    ]
}
let test_constr_multi = Constr (1, nat_inductive, [App (Lam ("x", Universe 0, Var "x"), Constr (0, nat_inductive, []))])
let test_ind_case = Ind (nat_inductive, 
                         Var "P", 
                         [App (Lam ("x", Universe 0, Var "x"), Var "base"); Var "step"], 
                         Constr (0, nat_inductive, []))
let test_higher_universe = App (Lam ("x", Universe 1, Var "x"), Universe 0)
let test_nested_pi = Pi ("x", Universe 0, Pi ("y", App (Lam ("z", Universe 0, Var "z"), Var "x"), Universe 0))
let test_no_reduction = App (Var "f", App (Var "g", Var "h"))
let list_inductive = {
    name = "List";
    params = [("A", Universe 0)];
    level = 0;
    constrs = [
        (0, Inductive {name = "List"; params = [("A", Universe 0)]; level = 0; constrs = []});  (* nil : List A *)
        (1, Pi ("x", Var "A", Pi ("xs", Inductive {name = "List"; params = [("A", Universe 0)]; level = 0; constrs = []}, Inductive {name = "List"; params = [("A", Universe 0)]; level = 0; constrs = []})))  (* cons : A → List A → List A *)
    ]
}
let test_list_cons = Constr (1, list_inductive, [Var "a"; App (Lam ("x", Universe 0, Constr (0, list_inductive, [])), Var "b")])
let test_double_shadow = App (App (Lam ("x", Universe 0, Lam ("x", Universe 0, Var "x")), Var "y"), Var "z")
let test_eta_pi = Lam ("x", Universe 0, App (Var "f", Var "x"))
let test_recursive_ind = Constr (1, nat_inductive, [Constr (1, nat_inductive, [App (Lam ("x", Universe 0, Var "x"), Constr (0, nat_inductive, []))])])
let test_pi_codomain = Pi ("x", Universe 0, App (Lam ("y", Universe 0, Var "x"), Var "z"))
let test_complex_ind = Ind (nat_inductive, 
                            Var "P", 
                            [Var "base"; App (Lam ("n", Universe 0, App (Lam ("ih", Universe 0, Var "ih"), Var "n")), Var "m")], 
                            Constr (1, nat_inductive, [Constr (0, nat_inductive, [])]))

let test_redundant_lam = Lam ("x", Universe 0, Lam ("y", Universe 0, Var "z"))



let () =
    print_endline "Original test1: ";
    print_endline (string_of_term test1);
    print_endline "Normalized test1: ";
    print_endline (string_of_term (normalize test1));
    print_endline "\nOriginal test2: ";
    print_endline (string_of_term test2);
    print_endline "Normalized test2 (should eta-reduce to f): ";
    print_endline (string_of_term (normalize test2));
    print_endline "Test loop (should terminate): ";
    print_endline (string_of_term (normalize test_loop));
    print_endline "Test capture (should avoid capture): ";
    print_endline (string_of_term (normalize test_capture));
    let tests = [
        ("test_higher_universe", test_higher_universe, "U0");
        ("test_nested_pi", test_nested_pi, {|Pi ("x", Universe 0, Pi ("y", Var "x", Universe 0))|});
        ("test_no_reduction", test_no_reduction, {|App (Var "f", App (Var "g", Var "h"))|});
        ("test_list_cons", test_list_cons, {|Constr (1, list_inductive, [Var "a"; Constr (0, list_inductive, [])])|});
        ("test_double_shadow", test_double_shadow, {|Var "z"|});
        ("test_eta_pi", test_eta_pi, {| Var "f" |});
        ("test_recursive_ind", test_recursive_ind, {| Constr (1, nat_inductive, [Constr (1, nat_inductive, [Constr (0, nat_inductive, [])])]) |});
        ("test_pi_codomain", test_pi_codomain, {| Pi ("x", Universe 0, Var "x") |});
        ("test_complex_ind", test_complex_ind, {| Ind (nat_inductive, Var "P", [Var "base"; Lam ("n", Universe 0, Var "n")], Constr (1, nat_inductive, [Constr (0, nat_inductive, [])])) |});
        ("test_redundant_lam", test_redundant_lam, {|Lam ("x", Universe 0, Lam ("y", Universe 0, Var "z")) |})
    ] in
    List.iter (fun (name, t, expected) ->
        Printf.printf "%s:\nOriginal: %s\nNormalized: %s\nExpected %s\n\n" 
            name 
            (string_of_term t) 
            (string_of_term (normalize t))
            expected
    ) tests