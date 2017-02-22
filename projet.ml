(* Section 3) Arbre Bicolore *)

(* Interface du type ordonné *)
module type Type_ordonne =
  sig
    type t
    val compare : t->t->int
    end

(* Type entier ordonné avec l'ordre usuel *)
module EntierOrdreNaturel =
    struct
        type t = int;;
        let compare e1 e2 =
            if e1 < e2 then -1
            else if e1 > e2 then 1
            else 0;;        
    end
        
(* Interface du module Ensemble *)
module type SignatureEnsemble = 
    functor (Type : Type_ordonne) ->
        sig
            type element = Type.t
            type abc
    
            val creer_vide: abc
      val est_vide : abc -> bool 
      val appartient_a : element -> abc -> bool
      val min : abc -> element
      val max : abc -> element
      val insert : element -> abc -> abc
      val delete : element -> abc -> abc
      val decouper_selon_min : abc -> element * abc
      val decouper_selon_max : abc -> element * abc
      val exploser : abc -> element * abc * abc
      val union : abc -> abc -> abc
      val intersection : abc -> abc -> abc
      val difference : abc -> abc -> abc
      val difference_symetrique : abc -> abc -> abc
      val liste_vers_ensemble : element list -> abc
      val ensemble_vers_liste : abc -> element list
      val est_inclus_dans : abc -> abc -> bool
      val est_egal_a : abc -> abc -> bool
      val appliquer_sur : (element -> element) -> abc -> abc
      val cardinal : abc -> int
      val iterer : (element -> 'a -> 'a) -> abc -> 'a -> 'a
      val est_verifiee_par_tous : (element -> bool) -> abc -> bool
      val est_verifiee_par_un : (element -> bool) -> abc -> bool
      val filtrer_selon : (element -> bool) -> abc -> abc
      val separer_selon : (element -> bool) -> abc -> abc * abc
      val separer_selon_pivot : element -> abc -> abc * bool * abc
end             

(* Module foncteur Ensemble, Les ensembles sont implémentés avec un arbre bicolore *)
(* Prend en paramètre un module 'Type' ayant comme interface 'Type_ordonne' *)
module Creer_mod_ens : SignatureEnsemble =
    functor (Type : Type_ordonne) ->
        struct
            open Type;;
            type element = t;;
            type color = Rouge | Noir | DoubleNoir;;
        type abc = Vide | VideNoir | Noeud of element * color * abc * abc;;
  
        type order = Lt | Eq | Gt;;
  
        let comp x y = 
                match (compare x y) with
                |   -1 -> Lt
                | 0 -> Eq
                | _ -> Gt;;

            let intComp x y =
                if x < y then
                    Lt
                else if x > y then
                    Gt
                else Eq;;

            let creer_vide = Vide;;

        let est_vide = function
        | Vide -> true
        | _ -> false;;
    
    let moins_noir noeud = 
        match noeud with
        | VideNoir -> Vide
        | Noeud(x, DoubleNoir, g, d) -> Noeud(x, Noir, g, d)
        | _ -> failwith "Impossible";;
    
    let plus_noir noeud =
        match noeud with
        | Noeud(x, Rouge, g, d) -> Noeud(x, Noir, g, d)
        | Noeud(x, Noir, g, d) -> Noeud(x, DoubleNoir, g, d)
        | Vide -> VideNoir
        | _ -> failwith "Impossible";;
    
    let moins_videNoir arbre =
        let rec aux arbre =
            match arbre with
            | Noeud(x, c, VideNoir, VideNoir) -> Noeud(x, c, Vide, Vide)
            | Noeud(x, c, VideNoir, d) -> Noeud(x, c, Vide, d)
            | Noeud(x, c, g, VideNoir) -> Noeud(x, c, g, Vide)
            | Noeud(x, c, g, d) -> Noeud(x, c, (aux g), (aux d))
            | Vide -> arbre
            | _ -> failwith "Impossible"
        in (aux arbre);;
    
    let valeur noeud =
        match noeud with
        | Noeud(x, _, _, _) -> x
        | Vide | VideNoir -> failwith "Impossible";;
    
    let sa_gauche noeud = 
        match noeud with
        | Noeud(_, _, g, _) -> g
        | _ -> failwith "Impossible";;
    
    let sa_droit noeud =
        match noeud with
        | Noeud(_, _, _, d) -> d
        | _ -> failwith "Impossible";;
    
    let estNoir noeud =
        match noeud with
        | Noeud(_, Noir, _, _) -> true
        | _ -> false;;
    
    let estRouge noeud =
        match noeud with
        | Noeud(_, Rouge, _, _) -> true
        | _ -> false;;
    
    let estDoubleNoir noeud =
        match noeud with
        | Noeud(_, DoubleNoir, _, _) -> true
        | VideNoir -> true
        | _ -> false;;
    
    let rec appartient_a x arbre =
        match arbre with
        | Noeud(e, _, g, d) -> 
            (match (comp x e) with
            | Lt -> (appartient_a x g)
            | Eq -> true
            | Gt -> (appartient_a x d))
        | _ -> false;;
    
    let rec min arbre =
        match arbre with
        | Noeud(x, _, Vide, _) -> x
        | Noeud(x, _, g, _) -> (min g)
        | _ -> failwith "Impossible";;
    
    let rec max arbre =
        match arbre with
        | Noeud(x, _, _, Vide) -> x
        | Noeud(x, _, _, d) -> (max d)
        | _ -> failwith "Impossible";; 
    
    let rec nb_noeuds = function
        | Vide | VideNoir -> 0
        | Noeud(_, _, g, d) -> 1 + (nb_noeuds g) + (nb_noeuds d);;
        
    let est_bicolore arbre =
        let rec est_abr arbre =
        match arbre with
        | Vide -> failwith "Erreur: arbre vide."
        | Noeud(e, c, Vide, Vide) -> (true, e, e)
        | Noeud(e, c, sg, Vide) -> let (est_bc, min, max) = (est_abr sg) in
                                                             (est_bc && max < e, min, e)
        | Noeud(e, c, Vide, sd) -> let (est_bc, min, max) = (est_abr sd) in
                                                             (est_bc && min > e, e, max)
        | Noeud(e, c, sg, sd) -> let (sg_bc, sg_min, sg_max) = (est_abr sg) 
                                                         and (sd_bc, sd_min, sd_max) = (est_abr sd) in
                                                         (sg_bc && sd_bc && sg_max < e && sd_min > e, sg_max, sd_min)
        | _ -> failwith "Impossible"
        
        and racine_est_noire arbre =
            match arbre with
            | Noeud(e, Noir, _, _) -> true
            | _ -> false
        
        and rouge_non_consecutifs arbre =
            let rec aux arbre couleur =
                match arbre with
                | Vide -> failwith "Erreur: arbre vide"
                | Noeud(e, Rouge, Vide, Vide) when couleur = Rouge -> false
                | Noeud(e, Rouge, Vide, Vide)
                | Noeud(e, Noir, Vide, Vide) -> true
                | Noeud(e, Rouge, sg, Vide) when couleur = Rouge -> false
                | Noeud(e, c, sg, Vide) -> (aux sg c)
                | Noeud(e, Rouge, Vide, sd) when couleur = Rouge -> false
                | Noeud(e, c, Vide, sd) -> (aux sd c)
                | Noeud(e, Rouge, sg, sd) when couleur = Rouge -> false
                | Noeud(e, c, sg, sd) -> let res_sg = (aux sg c) and res_sd = (aux sd c) in res_sg && res_sd
                | _ -> failwith "Impossible"
            in (aux arbre Noir)
        in
        
        let abr = match est_abr arbre with
        | (true, _, _) -> true
        | _ -> false
        
        in (abr && (racine_est_noire arbre) && (rouge_non_consecutifs arbre));;
    
    let rec equilibrage_ins = function
        | (z, Noir, Noeud(y, Rouge, Noeud(x, Rouge, a, b), c), d)
        | (z, Noir, Noeud(x, Rouge, a, Noeud(y, Rouge, b, c)), d)
        | (x, Noir, a, Noeud(z, Rouge, Noeud(y, Rouge, b, c), d))
        | (x, Noir, a, Noeud(y, Rouge, b, Noeud(z, Rouge, c, d))) ->
            Noeud(y, Rouge, Noeud(x, Noir, a, b), Noeud(z, Noir, c, d))
        | (a, b, c, d) -> Noeud(a, b, c, d);;
    
    let insert x s =
        let rec ins = function
            | Vide -> Noeud(x, Rouge, Vide, Vide)
            | Noeud(y, couleur, a, b) as s ->
                (match (comp x y) with
                | Lt -> (equilibrage_ins (y, couleur, (ins a), b))
                | Gt -> (equilibrage_ins (y, couleur, a, (ins b)))
                | Eq -> s)
            | _ -> failwith "Impossible"
            in
             match ins s with
            | Noeud(y, _, a, b) ->
                Noeud(y, Noir, a, b)
            | _ -> raise (Failure "Erreur lors de l'insertion");;
    
    let rec eq_del_g noeud =
        match noeud with
        | Noeud(y, Noir, f, Noeud(z, Rouge, g, d)) ->
            if (estDoubleNoir f) then
                Noeud(z, Noir, eq_del_g(Noeud(y, Rouge, f, g)), d)
            else    
                Noeud(y, Noir, f, Noeud(z, Rouge, g, d))
        | Noeud(y, c, f, Noeud(z, Noir, g, d)) ->
            if (estDoubleNoir f) then
                if (estNoir g) && (estNoir d) then
                    plus_noir(Noeud(y, c, (moins_noir f), Noeud(z, Rouge, g, d) ) )
                else if (estRouge g) && (estNoir d) then
                    eq_del_g(Noeud(y, c, f, Noeud((valeur g), Noir, (sa_gauche g), Noeud(z, Rouge, (sa_droit g), d))))
                else
                    Noeud(z, c, Noeud(y, Noir, (moins_noir f), g), (plus_noir d))
            else
                Noeud(y, c, f, Noeud(z, Noir, g, d))
      | Noeud(x, c, g, d) -> Noeud(x, c, g, d)
      | _ -> failwith "Impossible";;                
    
    let rec eq_del_d noeud =
        match noeud with
        | Noeud(y, Noir, Noeud(z, Rouge, g, d), f) ->
            if (estDoubleNoir f) then
                Noeud(z, Noir, g, eq_del_d(Noeud(y, Rouge, d, f)))
            else 
                Noeud(y, Noir, Noeud(z, Rouge, g, d), f)
        | Noeud(y, c, Noeud(z, Noir, g, d), f) ->
            if (estDoubleNoir f) then
                if (estNoir g) && (estNoir d) then
                    plus_noir(Noeud(y, c, Noeud(z, Rouge, g, d), (moins_noir f)))
                else if (estNoir g) && (estRouge d) then
                    eq_del_d(Noeud(y, c, Noeud((valeur d), Noir, Noeud(z, Rouge, g, (sa_gauche d)), (sa_droit d)), f))
                else
                    Noeud(z, c, plus_noir(g), Noeud(y, Noir, d, moins_noir(f))) 
            else
                Noeud(y, c, Noeud(z, Noir, g, d), f)
        | Noeud(x, c, g, d) -> Noeud(x, c, g, d)
        | _ -> failwith "Impossible";;      
                            
    
    let rec del e arbre =
        let rec aux arbre = 
            match arbre with
            | Noeud(x, Rouge, Vide, Vide) -> if (comp e x) = Eq then Vide else arbre
            | Noeud(x, Noir, Vide, Vide) -> if (comp e x) = Eq then VideNoir else arbre
            | Noeud(x, _, Vide, Noeud(y, _, g, d)) ->
                    if (comp e x) = Eq then Noeud(y, Noir, g, d)
                    else if (comp e y) = Eq then Noeud(x, Noir, Vide, Vide)
                    else arbre
            | Noeud(x, _, Noeud(y, _, g, d), Vide) ->
                    if(comp e x) = Eq then Noeud(y, Noir, g, d)
                    else if (comp e y) = Eq then Noeud(x, Noir, Vide, Vide)
                    else arbre
            | Noeud(x, c, g, d) ->
                    (match (comp e x) with
                    | Lt -> eq_del_g(Noeud(x, c, (aux g), d))
                    | Gt -> eq_del_d(Noeud(x, c, g, (aux d)))
                    | Eq -> let m = (min d)
                                    in eq_del_d(Noeud(m, c, g, (del m d))))
            | Vide -> arbre
            | _ -> failwith "Impossible"
        in (aux arbre);;
    
    let delete e arbre =
        match (del e arbre) with
        | Noeud(x, _, g, d) -> moins_videNoir(Noeud(x, Noir, g, d))
        | VideNoir -> Vide
        | _ -> failwith "Impossible";;
    
    let decouper_selon_min arbre =
        let m = (min arbre) in
        (m, (delete m arbre));;
    
    let decouper_selon_max arbre =
        let m = (max arbre) in
        (m, (delete m arbre));; 
    
    let exploser arbre =
        ((valeur arbre), (sa_gauche arbre), (sa_droit arbre));;
    
    let union a b =
        let rec aux a b =
            match a with
            | Vide | VideNoir -> b
            | Noeud(x, _, Vide, Vide) -> (insert x b)
            | Noeud(x, _, g, d) -> (aux g (aux d (insert x b)))
        in match (intComp (nb_noeuds a) (nb_noeuds b)) with 
        | Lt | Eq -> (aux a b) 
        | Gt -> (aux b a);;
    
    let intersection a b =
        let rec aux a b c =
            match a with
            | Vide | VideNoir -> c
            | Noeud(x, _, Vide, Vide) -> if (appartient_a   x b) then (insert x c) else c
            | Noeud(x, _, g, d) -> if(appartient_a x b) then
                                                            (aux g b (aux d b (insert x c)))
                                                         else
                                                            (aux g b (aux d b c))
        in match (intComp (nb_noeuds a) (nb_noeuds b)) with 
        | Lt | Eq -> (aux a b Vide) 
        | Gt -> (aux b a Vide);;
    
    let difference a b =
        let rec aux a b c =
            match a with
            | Vide | VideNoir -> c
            | Noeud(x, _, Vide, Vide) -> if (appartient_a   x b) then c else (insert x c)
            | Noeud(x, _, g, d) -> if(appartient_a x b) then                                                        
                                                            (aux g b (aux d b c))
                                                         else
                                                            (aux g b (aux d b (insert x c)))
            in (aux a b Vide);;
    
    let difference_symetrique a b = (union (difference a b) (difference b a));;
    
    let liste_vers_ensemble l =
        let rec aux l arbre =
            match l with
            | [] -> arbre
            | e::l -> (aux l (insert e arbre))
        in (aux l Vide);;
    
    let rec ensemble_vers_liste = function
        | Vide | VideNoir -> []
        | Noeud(x, _, g, d) -> (ensemble_vers_liste g) @ (x :: (ensemble_vers_liste d));;
    
    let est_inclus_dans e f =   ((union e f) = f);;
    
    let est_egal_a e f = (est_inclus_dans e f) && (est_inclus_dans f e);;
    
    let rec appliquer_sur g e =
            match e with
            | Vide -> Vide
            | VideNoir -> VideNoir
            | Noeud(x, c, Vide, Vide) -> Noeud((g x), c, Vide, Vide)
            | Noeud(x, c, sg, sd) -> Noeud((g x), c, (appliquer_sur g sg), (appliquer_sur g sd));;
    
    let rec cardinal e =
        match e with
        | Vide | VideNoir -> 0
        | Noeud(_, _, g, d) -> 1 + (cardinal g) + (cardinal d);;
    
    let rec iterer g e x =
        match e with
        | Vide | VideNoir -> x
        | Noeud(elt, _, sg, sd) -> g elt (iterer g sg (iterer g sd x));;
    
    let cardinal_iterer e =
        (iterer (function a -> function x -> x+1) e 0);;
                                            
    let est_verifiee_par_tous g e =
        let rec aux g e acc =
            match e with
            | Vide | VideNoir -> acc
            | Noeud(x, _, Vide, Vide) -> (g x)
            | Noeud(x, _, sg, sd) -> if (g x) then
                                                                (aux g sg (aux g sd (acc && true)))
                                                             else
                                                                false
        in (aux g e false);; 
    
    let est_verifiee_par_un g e =
        let rec aux g e acc =
            match e with
            | Vide | VideNoir -> acc
            | Noeud(x, _, Vide, Vide) -> if acc = true then acc else (g x)
            | Noeud(x, _, sg, sd) -> if (g x) then
                                                                (aux g sg (aux g sd true))
                                                             else
                                                                (aux g sg (aux g sd acc))
        in (aux g e false);;            
    
    let filtrer_selon g e =
        let rec aux g e acc =
            match e with
            | Vide | VideNoir -> acc
            | Noeud(x, _, Vide, Vide) -> if (g x) then (insert x acc) else acc
            | Noeud(x, _, sg, sd) -> if (g x) then (aux g sg (aux g sd (insert x acc)))
                                                             else (aux g sg (aux g sd acc))
        in (aux g e Vide);; 
    
    let separer_selon g e =
        let rec not_filtrer_selon g e acc =
            match e with
            | Vide | VideNoir -> acc
            | Noeud(x, _, Vide, Vide) -> if (g x) then acc else (insert x acc)
            | Noeud(x, _, sg, sd) -> if (g x) then (not_filtrer_selon g sg (not_filtrer_selon g sd acc))
                                                             else (not_filtrer_selon g sg (not_filtrer_selon g sd (insert x acc)))
        in ((filtrer_selon g e), (not_filtrer_selon g e Vide));;
                        
    let separer_selon_pivot x e =
        let inf = function y -> y < x
        and sup = function y -> y > x
        in
        
        ((filtrer_selon inf e), (appartient_a x e), (filtrer_selon sup e));;                            
        end


(* Ensemble d'entiers *)    
module Ens_int = Creer_mod_ens (EntierOrdreNaturel);;

(* Type ensemble d'ensemble d'entiers ordonné avec l'ordre lexicographique *)
module EnsembleOrdreLexicographique =
    struct
        type t = Ens_int.abc;;

        let compare e1 e2 =
            let l1 = (Ens_int.ensemble_vers_liste e1)
            and l2 = (Ens_int.ensemble_vers_liste e2) in
        
            let rec aux l1 l2 =
                match l1, l2 with
                | [], [] -> 0
                | [], e::l -> -1
                | e::l, [] -> 1
                | e::l, ee::ll when e < ee -> -1
                | e::l, ee::ll when e > ee -> 1
                | e::l, ee::ll when e = ee -> (aux l ll)
                | _ -> failwith "Error"
            in (aux l1 l2);;
    end


(* Ensemble d'ensemble d'entiers *)
module Ens_ens_int = Creer_mod_ens(EnsembleOrdreLexicographique);;


(* Section 4) Conversion *)

(* Définitions des types arbre bicolore & arbre 2-3-4 *)
type color = Rouge | Noir | DoubleNoir;;
type abic = VideAbic | VideNoir | Noeud of int * color * abic * abic;;

type a234 = VideA234
                        | Noeud2 of int * a234 * a234
                        | Noeud3 of (int * int) * a234 * a234 * a234
                        | Noeud4 of (int * int * int) * a234 * a234 * a234 * a234;;

(* Conversion arbre 2-3-4 -> arbre bicolore *)
let rec a234_vers_abic a =
    match a with
    | VideA234 -> VideAbic
    | Noeud2(e1, sa1, sa2) -> Noeud(e1, Noir, (a234_vers_abic sa1), (a234_vers_abic sa2))
    | Noeud3((e1, e2), sa1, sa2, sa3) -> Noeud(e2, Noir, Noeud(e1, Rouge, (a234_vers_abic sa1), (a234_vers_abic sa2)), (a234_vers_abic sa3))
    | Noeud4((e1, e2, e3), sa1, sa2, sa3, sa4) -> 
        Noeud(e2, Noir, Noeud(e1, Rouge, (a234_vers_abic sa1), (a234_vers_abic sa2)), Noeud(e3, Rouge, (a234_vers_abic sa3), (a234_vers_abic sa4)))
    ;;

(* Conversion arbre bicolore -> arbre 2-3-4 *)
let rec abic_vers_a234 a =
    match a with
    | VideAbic -> VideA234
    | Noeud(e2, Noir, Noeud(e1, Rouge, a1, a2), Noeud(e3, Rouge, a3, a4)) ->
            Noeud4((e1, e2, e3), (abic_vers_a234 a1), (abic_vers_a234 a2), (abic_vers_a234 a3), (abic_vers_a234 a4))
    | Noeud(e1, Noir, a1, Noeud(e2, Rouge, a2, a3))
    | Noeud(e2, Noir, Noeud(e1, Rouge, a1, a2), a3) -> Noeud3((e1, e2), (abic_vers_a234 a1), (abic_vers_a234 a2), (abic_vers_a234 a3))
    | Noeud(e, Noir, sg, sd) -> Noeud2(e, (abic_vers_a234 sg), (abic_vers_a234 sd))
    | _ -> failwith "Error";;


(* Section 5) Algorithmique des arbres 2-3-4 *)

(* Insertion d'un élément dans un arbre 2-3-4 *)

(* Fonctions secondaires *)
let compare e1 e2 =
    if e1 < e2 then -1
    else if e1 > e2 then 1
    else 0;;

let racine_a234 a =
    match a with
    | VideA234 -> VideA234
    | Noeud2(e, sg, sd) -> Noeud2(e, sg, sd)
    | Noeud3((e1, e2), a1, a2, a3) -> Noeud3((e1, e2), a1, a2, a3)
    | Noeud4((e1, e2, e3), a1, a2, a3, a4) -> Noeud4((e1, e2, e3), a1, a2, a3, a4);; 

(* Fonction d'insertion *)
let rec insert_a234 x a =
    match a with
    | VideA234 -> Noeud2(x, VideA234, VideA234)
    | Noeud2(e1, Noeud4((e2, e3, e4), a1, a2, a3, a4), a5) when (compare e1 x) = 1 ->
        (insert_a234 x (Noeud3((e3, e1), Noeud2(e2, a1, a2), Noeud2(e4, a3, a4), a5)))
    | Noeud2(e1, a1, Noeud4((e2, e3, e4), a2, a3, a4, a5)) when (compare e1 x) = -1->
        (insert_a234 x (Noeud3((e1, e3), a1, Noeud2(e2, a2, a3), Noeud2(e4, a4, a5))))
    | Noeud3((e1, e2), Noeud4((e3, e4, e5), a3, a4, a5, a6), a1, a2) when (compare e1 x) = 1 ->
        (match (compare e4 x) with
        | 1 -> Noeud4((e4, e1, e2), (insert_a234 x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6), a1, a2)
        | -1 -> Noeud4((e4, e1, e2), Noeud2(e3, a3, a4), (insert_a234 x (Noeud2(e5, a5, a6))), a1, a2)
        | _ -> a)
    | Noeud3((e1, e2), a1, Noeud4((e3, e4, e5), a3, a4, a5, a6), a2) when (compare e1 x) = -1 && (compare e2 x) = 1 ->
        (match (compare e4 x) with
        | 1 -> Noeud4((e1, e4, e2), a1, (insert_a234 x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6), a2)
        | -1 -> Noeud4((e1, e4, e2), a1, Noeud2(e3, a3, a4), (insert_a234 x (Noeud2(e5, a5, a6))), a2)
        | _ -> a)
    | Noeud3((e1, e2), a1, a2, Noeud4((e3, e4, e5), a3, a4, a5, a6)) when (compare e2 x) = -1 ->
        (match (compare e4 x) with
        | 1 -> Noeud4((e1, e2, e4), a1, a2, (insert_a234 x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6))
        | -1 -> Noeud4((e1, e2, e4), a1, a2, Noeud2(e3, a3, a4), (insert_a234 x (Noeud2(e5, a5, a6))))
        | _ -> a)
    | Noeud4((e1, e2, e3), a1, a2, a3, a4) as racine when ((racine_a234 a) = racine) ->
        (insert_a234 x (Noeud2(e2, Noeud2(e1, a1, a2), Noeud2(e3, a3, a4))))
    | Noeud4((e1, e2, e3), a1, a2, a3, a4) ->
        (match (compare e1 x) with
        | -1 -> (match (compare e2 x) with 
                        | -1 -> (match (compare e3 x) with
                                        | -1 -> Noeud4((e1, e2, e3), a1, a2, a3, (insert_a234 x a4))
                                        | 1 -> Noeud4((e1, e2, e3), a1, a2, (insert_a234 x a3), a4)
                                        | _ -> a)
                        | 1 -> Noeud4((e1, e2, e3), a1, (insert_a234 x a2), a3, a4)
                        | _ -> a)
        | 1 -> Noeud4((e1, e2, e3), (insert_a234 x a1), a2, a3, a4)
        | _ -> a)                   
    | Noeud2(e, VideA234, VideA234) -> 
        (match (compare e x) with
        | -1 -> Noeud3((e, x), VideA234, VideA234, VideA234)
        | 1 -> Noeud3((x, e), VideA234, VideA234, VideA234)
        | _ -> a) 
    | Noeud2(e, sg, sd) -> 
        (match (compare e x) with
        | 1 -> Noeud2(e, (insert_a234 x sg), sd) 
        | -1 ->  Noeud2(e, sg, (insert_a234 x sd))
        | _ -> a)
    | Noeud3((e1, e2), VideA234, VideA234, VideA234) -> 
        (match (compare e1 x) with
        | -1 -> 
            (match (compare e2 x) with
            | -1 -> Noeud4((e1, e2, x), VideA234, VideA234, VideA234, VideA234)
            | 1 -> Noeud4((e1, x, e2), VideA234, VideA234, VideA234, VideA234)
            | _ -> a)
        | 1 -> Noeud4((x, e1, e2), VideA234, VideA234, VideA234, VideA234)
        | _ -> a)
    |   Noeud3((e1, e2), sa1, sa2, sa3) ->
        (match(compare e1 x) with
        | -1 ->
            (match (compare e2 x) with
            | -1 -> Noeud3((e1, e2), sa1, sa2, (insert_a234 x sa3))
            | 1 -> Noeud3((e1, e2), sa1, (insert_a234 x sa2), sa3)
            | _ -> a)
        | 1 -> Noeud3((e1, e2), (insert_a234 x sa1), sa2, sa3)
        | _ -> a)
    ;;
    

(* Fonction de suppression d'un élément d'un arbre 234 (incomplete) 

let min_a234 a =
    let rec aux a min =
        match a with
        | VideA234 -> min
        | Noeud2(e, a1, a2) -> (aux a1 e)
        | Noeud3((e1, e2), a1, a2, a3) -> (aux a1 e1)
        | Noeud4((e1, e2, e3), a1, a2, a3, a4) -> (aux a1 e1)
    in (aux a 0);;

let max_a234 a =
    let rec aux a max =
        match a with
        | VideA234 -> max
        | Noeud2(e, a1, a2) -> (aux a2 e)
        | Noeud3((e1, e2), a1, a2, a3) -> (aux a3 e2)
        | Noeud4((e1, e2, e3), a1, a2, a3, a4) -> (aux a4 e3)
    in (aux a 0);;

let rec delete_a234 x a =
    match a with
    | VideA234 -> VideA234
    | Noeud2(e1, Noeud2(e2, a1, a2), Noeud2(e3, a3, a4)) ->
            (delete_a234 x (Noeud4((e1, e2, e3), a1, a2, a3, a4)))
    | Noeud3((x, e), VideA234, VideA234, VideA234)
    | Noeud3((e, x), VideA234, VideA234, VideA234) -> 
            Noeud2(e, VideA234, VideA234)
    | Noeud4((x, e1, e2), VideA234, VideA234, VideA234, VideA234)
    | Noeud4((e1, x, e2), VideA234, VideA234, VideA234, VideA234)
    | Noeud4((e1, e2, x), VideA234, VideA234, VideA234, VideA234) ->
            Noeud3((e1, e2), VideA234, VideA234, VideA234)
    | Noeud3((e1, e2), a1, a2, a3) ->
        (match (compare e1 x) with
        | -1 -> (match (compare e2 x) with
                        | -1 -> Noeud3((e1, e2), a1, a2, (delete_a234 x a3))
                        | 1 -> Noeud3((e1, e2), a1, (delete_a234 x a2), a3)
                        | _ -> a)) 
    ;; *)
    
    
(* Représentation des ensemble avec un arbre 2-3-4,
     les manipulations sont faite grâce à un arbre bicolore correspondant à l'arbre 2-3-4 courant 
     (utilisation des fonctions de conversion a234_vers_abic et abic_vers_a234 
*)

(* Interface du foncteur *)
module type SignatureEnsembleA234 = 
    functor (Type : Type_ordonne) ->
        sig
            type element = Type.t
            type a234
    
            val creer_vide: a234
      val est_vide : a234 -> bool 
      val appartient_a : element -> a234 -> bool
      val min : a234 -> element
      val max : a234 -> element
      val insert : element -> a234 -> a234
      val delete : element -> a234 -> a234
      val decouper_selon_min : a234 -> element * a234
      val decouper_selon_max : a234 -> element * a234
      val exploser : a234 -> element * a234 * a234
      val union : a234 -> a234 -> a234
      val intersection : a234 -> a234 -> a234
      val difference : a234 -> a234 -> a234
      val difference_symetrique : a234 -> a234 -> a234
      val liste_vers_ensemble : element list -> a234
      val ensemble_vers_liste : a234 -> element list
      val est_inclus_dans : a234 -> a234 -> bool
      val est_egal_a : a234 -> a234 -> bool
      val appliquer_sur : (element -> element) -> a234 -> a234
      val cardinal : a234 -> int
      val iterer : (element -> 'a -> 'a) -> a234 -> 'a -> 'a
      val est_verifiee_par_tous : (element -> bool) -> a234 -> bool
      val est_verifiee_par_un : (element -> bool) -> a234 -> bool
      val filtrer_selon : (element -> bool) -> a234 -> a234
      val separer_selon : (element -> bool) -> a234 -> a234 * a234
      val separer_selon_pivot : element -> a234 -> a234 * bool * a234
end

(* Module foncteur implémentant les ensembles ordonnés avec un arbre 2-3-4 *) 
module Creer_mod_ens_A234 : SignatureEnsembleA234 =
    functor (Type : Type_ordonne) ->
        struct
            open Type;;
            type element = t;;
        
      type color = Rouge | Noir | DoubleNoir;;
      type abic = VideAbic | VideNoir | Noeud of element * color * abic * abic;;
      
      type a234 = VideA234
                            | Noeud2 of element * a234 * a234
                            | Noeud3 of (element * element) * a234 * a234 * a234
                            | Noeud4 of (element * element * element) * a234 * a234 * a234 * a234;;
        
        type order = Lt | Eq | Gt;;
  
        let comp x y = 
            match (compare x y) with
            |   -1 -> Lt
            | 0 -> Eq
            | _ -> Gt;;
  
        let intComp x y =
            if x < y then
                Lt
            else if x > y then
                Gt
            else Eq;;
  
      let rec a234_vers_abic a =
        match a with
        | VideA234 -> VideAbic
        | Noeud2(e1, sa1, sa2) -> Noeud(e1, Noir, (a234_vers_abic sa1), (a234_vers_abic sa2))
        | Noeud3((e1, e2), sa1, sa2, sa3) -> Noeud(e2, Noir, Noeud(e1, Rouge, (a234_vers_abic sa1), (a234_vers_abic sa2)), (a234_vers_abic sa3))
        | Noeud4((e1, e2, e3), sa1, sa2, sa3, sa4) -> 
            Noeud(e2, Noir, Noeud(e1, Rouge, (a234_vers_abic sa1), (a234_vers_abic sa2)), Noeud(e3, Rouge, (a234_vers_abic sa3), (a234_vers_abic sa4)))
        ;;
      
      let rec abic_vers_a234 a =
        match a with
        | VideAbic -> VideA234
        | Noeud(e2, Noir, Noeud(e1, Rouge, a1, a2), Noeud(e3, Rouge, a3, a4)) ->
                Noeud4((e1, e2, e3), (abic_vers_a234 a1), (abic_vers_a234 a2), (abic_vers_a234 a3), (abic_vers_a234 a4))
        | Noeud(e1, Noir, a1, Noeud(e2, Rouge, a2, a3))
        | Noeud(e2, Noir, Noeud(e1, Rouge, a1, a2), a3) -> Noeud3((e1, e2), (abic_vers_a234 a1), (abic_vers_a234 a2), (abic_vers_a234 a3))
        | Noeud(e, Noir, sg, sd) -> Noeud2(e, (abic_vers_a234 sg), (abic_vers_a234 sd))
        | _ -> failwith "Error when converting abic to a234";;
  
  
        let creer_vide = VideA234;;
  
        let est_vide = function
        | VideA234 -> true
        | _ -> false;;
      
      let moins_noir noeud = 
        match noeud with
        | VideNoir -> VideAbic
        | Noeud(x, DoubleNoir, g, d) -> Noeud(x, Noir, g, d)
        | _ -> failwith "Impossible";;
      
      let plus_noir noeud =
        match noeud with
        | Noeud(x, Rouge, g, d) -> Noeud(x, Noir, g, d)
        | Noeud(x, Noir, g, d) -> Noeud(x, DoubleNoir, g, d)
        | VideAbic -> VideNoir
        | _ -> failwith "Impossible";;
      
      let moins_videNoir arbre =
        let rec aux arbre =
            match arbre with
            | Noeud(x, c, VideNoir, VideNoir) -> Noeud(x, c, VideAbic, VideAbic)
            | Noeud(x, c, VideNoir, d) -> Noeud(x, c, VideAbic, d)
            | Noeud(x, c, g, VideNoir) -> Noeud(x, c, g, VideAbic)
            | Noeud(x, c, g, d) -> Noeud(x, c, (aux g), (aux d))
            | VideAbic -> arbre
            | _ -> failwith "Impossible"
        in (aux arbre);;
      
      let valeur noeud =
        match noeud with
        | Noeud(x, _, _, _) -> x
        | VideAbic | VideNoir -> failwith "Impossible";;
      
      let sa_gauche noeud = 
        match noeud with
        | Noeud(_, _, g, _) -> g
        | _ -> failwith "Impossible";;
      
      let sa_droit noeud =
        match noeud with
        | Noeud(_, _, _, d) -> d
        | _ -> failwith "Impossible";;
      
      let estNoir noeud =
        match noeud with
        | Noeud(_, Noir, _, _) -> true
        | _ -> false;;
      
      let estRouge noeud =
        match noeud with
        | Noeud(_, Rouge, _, _) -> true
        | _ -> false;;
      
      let estDoubleNoir noeud =
        match noeud with
        | Noeud(_, DoubleNoir, _, _) -> true
        | VideNoir -> true
        | _ -> false;;
      
      let appartient_a x arbre =
            let rec aux x arbre =
            match arbre with
            | Noeud(e, _, g, d) -> 
                (match (comp x e) with
                | Lt -> (aux x g)
                | Eq -> true
                | Gt -> (aux x d))
            | _ -> false
            in (aux x (a234_vers_abic arbre));;
      
      let min arbre =
                let rec aux arbre =
            match arbre with
            | Noeud(x, _, VideAbic, _) -> x
            | Noeud(x, _, g, _) -> (aux g)
            | _ -> failwith "Impossible"
            in (aux (a234_vers_abic arbre));;
      
      let max arbre =
                let rec aux arbre = 
            match arbre with
            | Noeud(x, _, _, VideAbic) -> x
            | Noeud(x, _, _, d) -> (aux d)
            | _ -> failwith "Impossible"
                in (aux (a234_vers_abic arbre));; 
      
      let rec nb_noeuds = function
        | VideAbic | VideNoir -> 0
        | Noeud(_, _, g, d) -> 1 + (nb_noeuds g) + (nb_noeuds d);;
        
      let est_bicolore arbre =
        let rec est_abr arbre =
        match arbre with
        | VideAbic -> failwith "Erreur: arbre VideAbic."
        | Noeud(e, c, VideAbic, VideAbic) -> (true, e, e)
        | Noeud(e, c, sg, VideAbic) -> let (est_bc, min, max) = (est_abr sg) in
                                                             (est_bc && max < e, min, e)
        | Noeud(e, c, VideAbic, sd) -> let (est_bc, min, max) = (est_abr sd) in
                                                             (est_bc && min > e, e, max)
        | Noeud(e, c, sg, sd) -> let (sg_bc, sg_min, sg_max) = (est_abr sg) 
                                                         and (sd_bc, sd_min, sd_max) = (est_abr sd) in
                                                         (sg_bc && sd_bc && sg_max < e && sd_min > e, sg_max, sd_min)
        | _ -> failwith "Impossible"
        
        and racine_est_noire arbre =
            match arbre with
            | Noeud(e, Noir, _, _) -> true
            | _ -> false
        
        and rouge_non_consecutifs arbre =
            let rec aux arbre couleur =
                match arbre with
                | VideAbic -> failwith "Erreur: arbre VideAbic"
                | Noeud(e, Rouge, VideAbic, VideAbic) when couleur = Rouge -> false
                | Noeud(e, Rouge, VideAbic, VideAbic)
                | Noeud(e, Noir, VideAbic, VideAbic) -> true
                | Noeud(e, Rouge, sg, VideAbic) when couleur = Rouge -> false
                | Noeud(e, c, sg, VideAbic) -> (aux sg c)
                | Noeud(e, Rouge, VideAbic, sd) when couleur = Rouge -> false
                | Noeud(e, c, VideAbic, sd) -> (aux sd c)
                | Noeud(e, Rouge, sg, sd) when couleur = Rouge -> false
                | Noeud(e, c, sg, sd) -> let res_sg = (aux sg c) and res_sd = (aux sd c) in res_sg && res_sd
                | _ -> failwith "Impossible"
            in (aux arbre Noir)
        in
        
        let abr = match est_abr arbre with
        | (true, _, _) -> true
        | _ -> false
        
        in (abr && (racine_est_noire arbre) && (rouge_non_consecutifs arbre));;
    
    let racine_a234 a =
        match a with
        | VideA234 -> VideA234
        | Noeud2(e, sg, sd) -> Noeud2(e, sg, sd)
        | Noeud3((e1, e2), a1, a2, a3) -> Noeud3((e1, e2), a1, a2, a3)
        | Noeud4((e1, e2, e3), a1, a2, a3, a4) -> Noeud4((e1, e2, e3), a1, a2, a3, a4);; 
    
    let rec insert x a =
        match a with
        | VideA234 -> Noeud2(x, VideA234, VideA234)
        | Noeud2(e1, Noeud4((e2, e3, e4), a1, a2, a3, a4), a5) when (compare e1 x) = 1 ->
            (insert x (Noeud3((e3, e1), Noeud2(e2, a1, a2), Noeud2(e4, a3, a4), a5)))
        | Noeud2(e1, a1, Noeud4((e2, e3, e4), a2, a3, a4, a5)) when (compare e1 x) = -1->
            (insert x (Noeud3((e1, e3), a1, Noeud2(e2, a2, a3), Noeud2(e4, a4, a5))))
        | Noeud3((e1, e2), Noeud4((e3, e4, e5), a3, a4, a5, a6), a1, a2) when (compare e1 x) = 1 ->
            (match (compare e4 x) with
            | 1 -> Noeud4((e4, e1, e2), (insert x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6), a1, a2)
            | -1 -> Noeud4((e4, e1, e2), Noeud2(e3, a3, a4), (insert x (Noeud2(e5, a5, a6))), a1, a2)
            | _ -> a)
        | Noeud3((e1, e2), a1, Noeud4((e3, e4, e5), a3, a4, a5, a6), a2) when (compare e1 x) = -1 && (compare e2 x) = 1 ->
            (match (compare e4 x) with
            | 1 -> Noeud4((e1, e4, e2), a1, (insert x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6), a2)
            | -1 -> Noeud4((e1, e4, e2), a1, Noeud2(e3, a3, a4), (insert x (Noeud2(e5, a5, a6))), a2)
            | _ -> a)
        | Noeud3((e1, e2), a1, a2, Noeud4((e3, e4, e5), a3, a4, a5, a6)) when (compare e2 x) = -1 ->
            (match (compare e4 x) with
            | 1 -> Noeud4((e1, e2, e4), a1, a2, (insert x (Noeud2(e3, a3, a4))), Noeud2(e5, a5, a6))
            | -1 -> Noeud4((e1, e2, e4), a1, a2, Noeud2(e3, a3, a4), (insert x (Noeud2(e5, a5, a6))))
            | _ -> a)
        | Noeud4((e1, e2, e3), a1, a2, a3, a4) as racine when ((racine_a234 a) = racine) ->
            (insert x (Noeud2(e2, Noeud2(e1, a1, a2), Noeud2(e3, a3, a4))))
        | Noeud4((e1, e2, e3), a1, a2, a3, a4) ->
            (match (compare e1 x) with
            | -1 -> (match (compare e2 x) with 
                            | -1 -> (match (compare e3 x) with
                                            | -1 -> Noeud4((e1, e2, e3), a1, a2, a3, (insert x a4))
                                            | 1 -> Noeud4((e1, e2, e3), a1, a2, (insert x a3), a4)
                                            | _ -> a)
                            | 1 -> Noeud4((e1, e2, e3), a1, (insert x a2), a3, a4)
                            | _ -> a)
            | 1 -> Noeud4((e1, e2, e3), (insert x a1), a2, a3, a4)
            | _ -> a)                   
        | Noeud2(e, VideA234, VideA234) -> 
            (match (compare e x) with
            | -1 -> Noeud3((e, x), VideA234, VideA234, VideA234)
            | 1 -> Noeud3((x, e), VideA234, VideA234, VideA234)
            | _ -> a) 
        | Noeud2(e, sg, sd) -> 
            (match (compare e x) with
            | 1 -> Noeud2(e, (insert x sg), sd) 
            | -1 ->  Noeud2(e, sg, (insert x sd))
            | _ -> a)
        | Noeud3((e1, e2), VideA234, VideA234, VideA234) -> 
            (match (compare e1 x) with
            | -1 -> 
                (match (compare e2 x) with
                | -1 -> Noeud4((e1, e2, x), VideA234, VideA234, VideA234, VideA234)
                | 1 -> Noeud4((e1, x, e2), VideA234, VideA234, VideA234, VideA234)
                | _ -> a)
            | 1 -> Noeud4((x, e1, e2), VideA234, VideA234, VideA234, VideA234)
            | _ -> a)
        |   Noeud3((e1, e2), sa1, sa2, sa3) ->
            (match(compare e1 x) with
            | -1 ->
                (match (compare e2 x) with
                | -1 -> Noeud3((e1, e2), sa1, sa2, (insert x sa3))
                | 1 -> Noeud3((e1, e2), sa1, (insert x sa2), sa3)
                | _ -> a)
            | 1 -> Noeud3((e1, e2), (insert x sa1), sa2, sa3)
            | _ -> a)
        ;;
      
      let rec eq_del_g noeud =
        match noeud with
        | Noeud(y, Noir, f, Noeud(z, Rouge, g, d)) ->
            if (estDoubleNoir f) then
                Noeud(z, Noir, eq_del_g(Noeud(y, Rouge, f, g)), d)
            else    
                Noeud(y, Noir, f, Noeud(z, Rouge, g, d))
        | Noeud(y, c, f, Noeud(z, Noir, g, d)) ->
            if (estDoubleNoir f) then
                if (estNoir g) && (estNoir d) then
                    plus_noir(Noeud(y, c, (moins_noir f), Noeud(z, Rouge, g, d) ) )
                else if (estRouge g) && (estNoir d) then
                    eq_del_g(Noeud(y, c, f, Noeud((valeur g), Noir, (sa_gauche g), Noeud(z, Rouge, (sa_droit g), d))))
                else
                    Noeud(z, c, Noeud(y, Noir, (moins_noir f), g), (plus_noir d))
            else
                Noeud(y, c, f, Noeud(z, Noir, g, d))
        | Noeud(x, c, g, d) -> Noeud(x, c, g, d)
        | _ -> failwith "Impossible";;              
      
      let rec eq_del_d noeud =
        match noeud with
        | Noeud(y, Noir, Noeud(z, Rouge, g, d), f) ->
            if (estDoubleNoir f) then
                Noeud(z, Noir, g, eq_del_d(Noeud(y, Rouge, d, f)))
            else 
                Noeud(y, Noir, Noeud(z, Rouge, g, d), f)
        | Noeud(y, c, Noeud(z, Noir, g, d), f) ->
            if (estDoubleNoir f) then
                if (estNoir g) && (estNoir d) then
                    plus_noir(Noeud(y, c, Noeud(z, Rouge, g, d), (moins_noir f)))
                else if (estNoir g) && (estRouge d) then
                    eq_del_d(Noeud(y, c, Noeud((valeur d), Noir, Noeud(z, Rouge, g, (sa_gauche d)), (sa_droit d)), f))
                else
                    Noeud(z, c, plus_noir(g), Noeud(y, Noir, d, moins_noir(f))) 
            else
                Noeud(y, c, Noeud(z, Noir, g, d), f)
        | Noeud(x, c, g, d) -> Noeud(x, c, g, d)
        | _ -> failwith "Impossible";;      
                            
      
      let rec del e arbre =
        let rec aux arbre = 
            match arbre with
            | Noeud(x, Rouge, VideAbic, VideAbic) -> if (comp e x) = Eq then VideAbic else arbre
            | Noeud(x, Noir, VideAbic, VideAbic) -> if (comp e x) = Eq then VideNoir else arbre
            | Noeud(x, _, VideAbic, Noeud(y, _, g, d)) ->
                    if (comp e x) = Eq then Noeud(y, Noir, g, d)
                    else if (comp e y) = Eq then Noeud(x, Noir, VideAbic, VideAbic)
                    else arbre
            | Noeud(x, _, Noeud(y, _, g, d), VideAbic) ->
                    if(comp e x) = Eq then Noeud(y, Noir, g, d)
                    else if (comp e y) = Eq then Noeud(x, Noir, VideAbic, VideAbic)
                    else arbre
            | Noeud(x, c, g, d) ->
                    (match (comp e x) with
                    | Lt -> eq_del_g(Noeud(x, c, (aux g), d))
                    | Gt -> eq_del_d(Noeud(x, c, g, (aux d)))
                    | Eq -> let m = (min (abic_vers_a234 d))
                                    in eq_del_d(Noeud(m, c, g, (del m d))))
            | VideAbic -> arbre
            | _ -> failwith "Impossible"
        in (aux arbre);;
      
      let delete e arbre =
        match (del e (a234_vers_abic arbre)) with
        | Noeud(x, _, g, d) -> (abic_vers_a234 (moins_videNoir(Noeud(x, Noir, g, d))))
        | VideNoir -> VideA234
        | _ -> failwith "Impossible";;
      
      let decouper_selon_min arbre =
        let m = (min arbre) in
        (m, (delete m arbre));;
      
      let decouper_selon_max arbre =
        let m = (max arbre) in
        (m, (delete m arbre));; 
      
      let exploser arbre =
        ((valeur (a234_vers_abic arbre)), (abic_vers_a234 (sa_gauche (a234_vers_abic arbre))), (abic_vers_a234 (sa_droit (a234_vers_abic arbre))));;
      
        let union arbre_a arbre_b =
        let rec aux a b =
            match a with
            | VideAbic | VideNoir -> b
            | Noeud(x, _, VideAbic, VideAbic) -> (a234_vers_abic (insert x (abic_vers_a234 b)))
            | Noeud(x, _, g, d) -> (aux g (aux d (a234_vers_abic (insert x (abic_vers_a234 b)))))
        in match (intComp (nb_noeuds (a234_vers_abic arbre_a)) (nb_noeuds (a234_vers_abic arbre_b))) with 
        | Lt | Eq -> (abic_vers_a234 (aux (a234_vers_abic arbre_a) (a234_vers_abic arbre_b))) 
        | Gt -> (abic_vers_a234 (aux (a234_vers_abic arbre_b) (a234_vers_abic arbre_a)));;
      
      let intersection a b =
        let rec aux a b c =
            match a with
            | VideAbic | VideNoir -> c
            | Noeud(x, _, VideAbic, VideAbic) -> if (appartient_a   x (abic_vers_a234 b)) then (a234_vers_abic (insert x (abic_vers_a234 c))) else c
            | Noeud(x, _, g, d) -> if(appartient_a x (abic_vers_a234 b)) then
                                                            (aux g b (aux d b (a234_vers_abic (insert x (abic_vers_a234 c)))))
                                                         else
                                                            (aux g b (aux d b c))
        in match (intComp (nb_noeuds (a234_vers_abic a)) (nb_noeuds (a234_vers_abic b))) with 
        | Lt | Eq -> (abic_vers_a234 (aux (a234_vers_abic a) (a234_vers_abic b) VideAbic)) 
        | Gt -> (abic_vers_a234 (aux (a234_vers_abic b) (a234_vers_abic a) VideAbic));;
      
      let difference a b =
        let rec aux a b c =
            match a with
            | VideAbic | VideNoir -> c
            | Noeud(x, _, VideAbic, VideAbic) -> if (appartient_a   x (abic_vers_a234 b)) then c else (a234_vers_abic (insert x (abic_vers_a234 c)))
            | Noeud(x, _, g, d) -> if(appartient_a x (abic_vers_a234 b)) then                                                       
                                                            (aux g b (aux d b c))
                                                         else
                                                            (aux g b (aux d b (a234_vers_abic (insert x (abic_vers_a234 c)))))
            in (abic_vers_a234 (aux (a234_vers_abic a) (a234_vers_abic b) VideAbic));;
      
      let difference_symetrique a b = (union (difference a b) (difference b a));;
      
      let liste_vers_ensemble l =
        let rec aux l arbre =
            match l with
            | [] -> arbre
            | e::l -> (aux l (insert e arbre))
        in (aux l VideA234);;
      
      let ensemble_vers_liste a =
            let rec ens_vers_liste a = 
                match a with
            | VideAbic | VideNoir -> []
            | Noeud(x, _, g, d) -> (ens_vers_liste g) @ (x :: (ens_vers_liste d))
            in (ens_vers_liste (a234_vers_abic a));;
  
     
      let est_inclus_dans e f = ((union e f) = f);;
      
      let est_egal_a e f = (est_inclus_dans e f) && (est_inclus_dans f e);;
      
      let appliquer_sur g e =
            let rec aux g e =
            match e with
            | VideAbic -> VideAbic
            | VideNoir -> VideNoir
            | Noeud(x, c, VideAbic, VideAbic) -> Noeud((g x), c, VideAbic, VideAbic)
            | Noeud(x, c, sg, sd) -> Noeud((g x), c, (aux g sg), (aux g sd))
            in (abic_vers_a234 (aux g (a234_vers_abic e)));;
      
      let cardinal e =
            let rec aux e =
            match e with
            | VideAbic | VideNoir -> 0
            | Noeud(_, _, g, d) -> 1 + (aux g) + (aux d)
            in (aux (a234_vers_abic e));;
      
      let iterer g e x =
            let rec aux g e x =
            match e with
            | VideAbic | VideNoir -> x
            | Noeud(elt, _, sg, sd) -> g elt (aux g sg (aux g sd x))
            in (aux g (a234_vers_abic e) x);;
      
      let cardinal_iterer e =
        (iterer (function a -> function x -> x+1) e 0);;
                                            
      let est_verifiee_par_tous g e =
        let rec aux g e acc =
            match e with
            | VideAbic | VideNoir -> acc
            | Noeud(x, _, VideAbic, VideAbic) -> (g x)
            | Noeud(x, _, sg, sd) -> if (g x) then
                                                                (aux g sg (aux g sd (acc && true)))
                                                             else
                                                                false
        in (aux g (a234_vers_abic e) false);; 
      
      let est_verifiee_par_un g e =
        let rec aux g e acc =
            match e with
            | VideAbic | VideNoir -> acc
            | Noeud(x, _, VideAbic, VideAbic) -> if acc = true then acc else (g x)
            | Noeud(x, _, sg, sd) -> if (g x) then
                                                                (aux g sg (aux g sd true))
                                                             else
                                                                (aux g sg (aux g sd acc))
        in (aux g (a234_vers_abic e) false);;           
      
      let filtrer_selon g e =
        let rec aux g e acc =
            match e with
            | VideAbic | VideNoir -> acc
            | Noeud(x, _, VideAbic, VideAbic) -> if (g x) then (insert x acc) else acc
            | Noeud(x, _, sg, sd) -> if (g x) then (aux g sg (aux g sd (insert x acc)))
                                                             else (aux g sg (aux g sd acc))
        in (aux g (a234_vers_abic e) VideA234);;
      
      let separer_selon g e =
        let rec not_filtrer_selon g e acc =
            match e with
            | VideAbic | VideNoir -> acc
            | Noeud(x, _, VideAbic, VideAbic) -> if (g x) then acc else (insert x acc)
            | Noeud(x, _, sg, sd) -> if (g x) then (not_filtrer_selon g sg (not_filtrer_selon g sd acc))
                                                             else (not_filtrer_selon g sg (not_filtrer_selon g sd (insert x acc)))
        in ((filtrer_selon g e), (not_filtrer_selon g (a234_vers_abic e) VideA234));;
                                                
      let separer_selon_pivot x e =
        let inf = function y -> y < x
        and sup = function y -> y > x
        in
        
        ((filtrer_selon inf e), (appartient_a x e), (filtrer_selon sup e));;
end

(* Ensemble d'entiers représenté avec un arbre 2-3-4 *)
module Ens_int_A234 = Creer_mod_ens_A234(EntierOrdreNaturel);;

(* Ensemble d'ensembles d'entiers représenté avec un arbre 2-3-4 *)
module EnsembleOrdreLexicographiqueA234 =
    struct
        type t = Ens_int_A234.a234;;

        let compare e1 e2 =
            let l1 = (Ens_int_A234.ensemble_vers_liste e1)
            and l2 = (Ens_int_A234.ensemble_vers_liste e2) in
        
            let rec aux l1 l2 =
                match l1, l2 with
                | [], [] -> 0
                | [], e::l -> -1
                | e::l, [] -> 1
                | e::l, ee::ll when e < ee -> -1
                | e::l, ee::ll when e > ee -> 1
                | e::l, ee::ll when e = ee -> (aux l ll)
                | _ -> failwith "Error"
            in (aux l1 l2);;
    end

(* Ensemble d'ensembles d'entiers représenté avec un arbre 2-3-4 *)
module Ens_ens_int_A234 = Creer_mod_ens_A234(EnsembleOrdreLexicographiqueA234);;

(* Exemples *)

let ens = (Ens_int_A234.insert 10 Ens_int_A234.creer_vide);;
let ens = (Ens_int_A234.insert 3 ens);;
let ens = (Ens_int_A234.insert 7 ens);;
let ens = (Ens_int_A234.insert 4 ens);;
let ens = (Ens_int_A234.insert 9 ens);;
(Ens_int_A234.ensemble_vers_liste ens);;

(Ens_int_A234.appartient_a 10 ens);;
(Ens_int_A234.appartient_a 8 ens);;
(Ens_int_A234.min ens);;
(Ens_int_A234.max ens);;
(Ens_int_A234.cardinal ens);;

let ens_ens = (Ens_ens_int_A234.insert ens Ens_ens_int_A234.creer_vide);;
(Ens_ens_int_A234.ensemble_vers_liste ens_ens);;
