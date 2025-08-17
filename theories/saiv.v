(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra unstable boolp interval_inference.
From mathcomp Require Import classical_sets functions cardinality fsbigop reals.
From mathcomp Require Import ereal topology normedtype sequences real_interval.
From mathcomp Require Import esum measure ess_sup_inf lebesgue_measure.
From mathcomp Require Import lebesgue_integral numfun exp convex.
From mathcomp Require Export hoelder.
From mathcomp Require Import lra.

(**md**************************************************************************)
(* # eHoelder's Inequality                                                     *)
(*                                                                            *)
(* This file provides the Lp-norm, eHoelder's inequality and its consequences, *)
(* most notably Minkowski's inequality, the convexity of the power function,  *)
(* and a definition of Lp-spaces.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*         'N[mu]_p[f] == the Lp-norm of f with measure mu                    *)
(*         conjugate p == a real number q such that p^-1 + q^-1 = 1 when      *)
(*                        p is real, otherwise conjugate +oo = 1 and          *)
(*                        conjugate -oo = 0                                   *)
(* ```                                                                        *)
(*                                                                            *)
(* Lp-spaces and properties of Lp-norms:                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*    finite_norm mu p f := the L-norm of real-valued function f is finite    *)
(*                          The parameter p is an extended real.              *)
(*        LfunType mu p1 == type of measurable functions f with a finite      *)
(*                          L-norm                                            *)
(*                          p1 is a proof that the extended real number p is  *)
(*                          greater or equal to 1.                            *)
(*                          The HB class is Lfun.                             *)
(*            f \in lfun == holds for f : LfunType mu p1                      *)
(*            Lequiv f g == f is equal to g almost everywhere                 *)
(*                          The functions f and g have type LfunType mu p1.   *)
(*                          Lequiv is made a canonical equivalence relation.  *)
(*      LspaceType mu p1 == type of the elements of the Lp space for the      *)
(*                          measure mu                                        *)
(*          mu.-Lspace p == Lp space as a set                                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "'N[ mu ]_ p [ F ]"
  (at level 5, F at level 36, mu at level 10,
  format "'[' ''N[' mu ]_ p '/  ' [ F ] ']'").
(* for use as a local notation when the measure is in context: *)
Reserved Notation "'N_ p [ F ]"
  (at level 5, F at level 36, format "'[' ''N_' p '/  ' [ F ] ']'").
Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").

Declare Scope Lnorm_scope.
Local Open Scope ereal_scope.

Definition geo_mean {d} {T : measurableType d} {R : realType} 
  (P : probability T R) (f : T -> \bar R) := expeR (\int[P]_x (lne (f x)))%E. 

HB.lock Definition Lnorm {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (\int[mu]_x `|f x| `^ p%:E) `^ p^-1%:E
  | +oo%E => if mu [set: T] > 0 then ess_sup mu (abse \o f) else 0
  | -oo%E => if mu [set: T] > 0 then ess_inf mu (abse \o f) else 0
  end.
Canonical locked_Lnorm := Unlockable Lnorm.unlock.
Arguments Lnorm {d T R} mu p f.

Definition pmean {d} {T : measurableType d} {R : realType} 
  (P : probability T R) (p : \bar R) (f : T -> \bar R) := 
  if p == 0 then geo_mean P f else Lnorm P p f.

(*Definition hpmean {d} {T : measurableType d} {R : realType} 
  (P : probability T R) (p : \bar R) (f : T -> \bar R) := 
  (pmean P p ((poweR ^~ -1%:E) \o f)) `^ -1%:E.
*)
Local Close Scope ereal_scope.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnorm_1 f : 'N_1[f] = \int[mu]_x `|f x|.
Proof.
rewrite unlock invr1//poweRe1//;under eq_integral do [rewrite poweRe1//=] => //.
exact: integral_ge0.
Qed.

Lemma Lnorm_abse f p :
  'N_p[abse \o f] = 'N_p[f].
Proof.
rewrite unlock/=.
have -> : (abse \o (abse \o f)) = abse \o f.
  by apply: funext => x/=; rewrite abse_id.
case: p => [r|//|//].
by under eq_integral => x _ do rewrite abse_id.
Qed.

Lemma eq_Lnorm p f g : f =1 g -> 'N_p[f] = 'N_p[g].
Proof. by move=> fg; congr Lnorm; apply/eq_fun => ?; rewrite /= fg. Qed.

Lemma poweR_Lnorm f r : (0 < r)%R ->
  'N_r%:E[f] `^ r%:E = \int[mu]_x (`| f x | `^ r%:E).
Proof.
move => r0; rewrite unlock ?(gt_eqF r0); move : r0.
have : 0 <= \int[mu]_x (`| f x | `^ r%:E); 
    first by apply integral_ge0 => ? _; rewrite poweR_ge0.
case intfx : (\int[mu]_x  `|f x| `^ r%:E) => [x||] // x0 r0; last first. 
- rewrite !poweRyPe ?invr_gt0 ?lte_fin ?invr_gt0 => //.
- rewrite !poweR_EFin; f_equal. rewrite -powRrM mulVf;
  last by rewrite negbT // eq_sym; apply (lt_eqF r0).
  apply powRr1; by move : x0; rewrite lee_fin.
Qed.

Lemma oppe_Lnorm f p : 'N_p[\- f]%E = 'N_p[f].
Proof.
have NfE : abse \o (\- f) = abse \o f.
  by apply/funext => x /=; rewrite abseN.
rewrite unlock /Lnorm NfE; case: p => /= [r|//|//].
by under eq_integral => x _ do rewrite abseN.
Qed.

Lemma Lnorm_ge0 p f : 0 <= 'N_p[f].
Proof.
rewrite unlock; move: p => [r/=|/=|//]; first exact: poweR_ge0.
- by case: ifPn=>// /ess_sup_gee ->//;apply /aeW => ?/=.
- by case: ifPn=>// muT0; apply/ess_infP/nearW => ?/=.
Qed.

Lemma measurable_poweR p :
      measurable_fun [set: \bar R] (poweR ^~ p).
  Proof.
  move: p => [r||]; move => _ /= B mB; rewrite setIidr; last by apply subsetT.
  - rewrite [X in measurable X]
    (_ : (poweR^~ r%:E @^-1` B) = 
    if (r == 0%R) then 
      (if 1 \in B then [set : \bar R] else set0) 
    else
      EFin @` ( @powR R ^~ r @^-1` (fine @` (B `\` [set -oo; +oo])))  
      `|` (if (0 < r)%R then (B `&` [set +oo]) 
          else if 0 \in B then [set +oo] else set0)
      `|` (if 1 \in B then [set -oo] else set0)
    ); first last.
    + case : (ltgtP 0%R r) => r0; repeat case : ifPn; 
      repeat try (move => /set_mem ?) + (rewrite notin_setE => ?);
      apply /seteqP; split => [[s||] //= |x //=];
      rewrite ?poweR_EFin.
      all: try (by left;left; exists s => //; exists (s `^ r)%:E => //; 
          split => //; rewrite not_orE; split).
      all: try (by right + by (rewrite ?poweRNye // ?poweRyPe //;left;right) 
        + by move => [[[a [[z||] [Bz /not_orP 
          [zneqNy zneqy] //= zar <-]]]|H]|xNy];
          rewrite -lte_fin in r0; try (case H => + xy); 
          rewrite ?poweR_EFin -?zar ?xy ?H ?(poweRyPe r0) ?(poweRyNe r0) ?xNy 
          ?poweRNye) + by (rewrite ?(gt_eqF r0) ?r0 => //; left; right)
        + by rewrite poweRyNe + by rewrite -r0 ?poweRe0 ?powRr0.
    + case : (ltgtP 0%R r) => r0; repeat case : ifPn; 
      try move => /set_mem B1; try rewrite notin_setE => nB1;
      try move => /set_mem B0; try rewrite notin_setE => nB0;
      repeat apply : measurableU => //=; try apply: measurable_image_EFin;
      try rewrite -[X in measurableR X] setTI; try apply: @measurable_powR =>//;
      by try exact: measurable_image_fine; try exact: measurableI => //=.
  - rewrite [X in measurable X]
    (_ : (poweR^~ +oo @^-1` B) = 
    (if 0 \in B then `[0, 1[%classic else set0) `|`
    (if 1 \in B then `[-oo, 0[ `|` [set 1] else set0) `|`
    (if +oo \in B then `]1, +oo]%classic else set0)).
  3: rewrite [X in measurable X]
  (_ : (poweR^~ -oo @^-1` B) = 
    (if 0 \in B then `]1, +oo[%classic `|` [set 0] else set0) `|`
    (if 1 \in B then `[-oo, 0[%classic `|` [set 1] else set0) `|`
    (if +oo \in B then `]0, 1[%classic else set0)).
  1,3: try repeat case : ifPn; try rewrite notin_setE; 
  do 3 (move=> /set_mem ?) + (move=> ?); 
  repeat apply /measurableU => //=; apply /emeasurable_itv.
  all: repeat case : ifPn; do 3 (move=> /set_mem ?) + (rewrite notin_setE=> ?); 
  apply /seteqP; split => [[r||] //=| [r||] //=]; rewrite ?in_itv //= ?leey 
  ?ltry ?ltNyr ?leNye //= ?trueE ?falseE ?orB //= ?andC ?andbT; 
  try by rewrite !orB + rewrite lt0_poweR ?real_ltNyr 
    + rewrite poweRey_gt1 ?real_ltry.
  all: rewrite -?eq_opE; try (case:(ltgtP 1 r%:E)=>r1; case:(ltgtP 0 r%:E)=>r0);
  rewrite ?andbT ?andbF ?trueE ?falseE ?orB -?r1 ?(poweRey_gt1 r1) 
  ?(poweReNy_gt1 r1)?poweR1e -?r0 //= ?poweR0e ?(lt0_poweR _ r0) 
  ?(poweReNy_gt1 ( @ltry _ 1)) ?poweRey_lt1 ?poweReNy_lt1
  ?r1 ?r0 ?(ltW r0) -?r0 //= ?r0 //=; 
  by right + by move=> ?; rewrite poweRey_lt1 ?r1 ?andbT
    + by have := lt_trans r1 r0; rewrite lte_fin ltr10.
  Qed.
End Lnorm_properties.

#[global]
Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnorm_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f) : ereal_scope.

Section Lmean_properties.
Context d {X : measurableType d} {R : realType}.
Variable P : probability X R.
Local Open Scope ereal_scope.
Implicit Types  (f g : X -> \bar R).
Implicit Types (n p q  : \bar R).
Variable (phi : X -> \bar R) (phi0 : forall x, 0 <= phi x) (mphi : measurable_fun [set: X] phi).
Variable (psi : X -> X -> \bar R) (psi0 : forall x y, 0 <= psi x y) (mpsix : forall x , measurable_fun [set: X] (psi x)).

Definition cdual (x : \bar R) := (if (x == 0)%E then +oo else (x `^ -1%:E)).

Local Notation "'N_ p [ f ]" := (Lnorm P p f).
Local Notation "x ^'" := (cdual x).
Local Notation "x *' y" := (((x ^')*(y ^'))^')(at level 3).
Local Notation "y -o x" := (x *' (y ^')) (at level 5).
Local Notation "'forall_  p f " := (pmean P p f).
Local Notation "'exists_  p f " := (('forall_p (fun y => (f y)^'))^').

Let measurableT_comp_poweR t f :
  measurable_fun [set: X] f -> measurable_fun setT (fun x => f x `^ t).
  Proof. 
  move=> ?; apply ( @measurableT_comp _ _ _ _ _ _ ( @poweR (R) ^~ t))=> //=.
  exact: measurable_poweR.
  Qed.

Lemma idem_dual w : 0 <= w -> (w^')^' = w.
Proof.
  move=> w0.
  rewrite /cdual; repeat case : ifPn.
  - by move=> /eqP -> /eqP ->.
  - by move=> /negPf neqp0; rewrite poweR_eq0y ?neqp0 ?andbF //=; 
    move=> /andP [] /eqP ->.
  - by move=> /eqP ->; rewrite poweRyNe.
  - move: w w0 => [r||] //; last first.
    -- by rewrite poweRyNe // eq_refl.
    -- move=> r0 neqr0; rewrite !poweR_EFin -powRrM (_ : (-1 * -1)%R = 1%R)
      ?powRr1 ?mulN1r//=; nra.
Qed.

Lemma times_dual p q : (0 <= p) -> (0 <= q) -> p * q = ((p^') *' (q^'))^'.
Proof.
  move=> p0 q0; rewrite !idem_dual //=.
  apply /mule_ge0 => //.
Qed.

(*
Lemma parC p q : p *' q = q *' p.
Proof.
  rewrite /cdual; repeat case: ifPn => //=; rewrite muleC => /eqP //=.
  all: try move => /eqP -> //=.
  - 

Lemma pary0 p :  p *' +oo = +oo.

Lemma par0 p :  p *' 0 = 0.
Proof.
  rewrite /cdual; repeat case : ifPn => /eqP //=.
  - by move=> _ _  <-; rewrite mulyy.
  - move => _ ; case : (ltgtP p 0); try move=> // ->; last first.
      rewrite poweR0e ?mul0e.
*)

Lemma forall_gt0 p f : (0 < p) -> 0%R <= 'forall_ p (fun y => f y).
Proof.
  move=> p0 //=; rewrite /pmean (_ : p == 0%R = false).
  by rewrite Lnorm_ge0. 
  by apply /negP => /eqP; move: p0 => /[swap] ->; rewrite ltxx.
Qed.

Lemma Duality p x : 
  (0 < p) -> 'forall_p (psi x) = ('exists_p (fun y => (psi x y)^'))^'. 
Proof.
  by  move=> ?; rewrite (*this is true since ...*)
    idem_dual //= (*the dual is idempotent and ...*)
    ?forall_gt0 //; (*the pmean is always non negative and ...*)
  under eq_fun do rewrite (*inside the pmean...*)
    idem_dual //. (*the dual is idempotent*)
Qed.

Lemma pmean_pair_dist p x e : (0 <= e) -> (0 < p) -> 
  e *' ('forall_p (psi x)) = 'forall_p (fun y => e *' (psi x y)).
Proof.
  move=> e0 p0; rewrite /pmean //= (_ : p == 0%R = false); last first.
    by apply /negP => /eqP; move: (p0) => /[swap] ->; rewrite ltxx.
move: p p0 => [r||]; rewrite unlock; try case : ifPn; rewrite mul.
  rewrite unlock.
  move: e e0 => [r||] //= e0.

Lemma inv_pmeanD: 
  forall x, (0 < p) -> 
  (phi x) -o ('forall_p (psi x)) = 'forall_p (fun y => (phi x) -o (psi x y)).

Lemma inv_pmeanD: 
  forall x, (0 < p) -> 
  (phi x) -o ('forall_p (psi x)) = 'forall_p (fun y => (phi x) -o (psi x y)).
Proof.
  move: p => [r||] //= x; rewrite /pmean unlock//=.
  - case: (ltgtP r%:E 0%:E) => // r0 _; apply /eqP; rewrite eq_sym.
    under eq_integral do rewrite abseM poweRM ?lt0r_neq0 //.
    rewrite ge0_integralZr //; last first; 
    [apply poweR_ge0 | move => ? ?; apply poweR_ge0
    |by apply /measurableT_comp_poweR/measurableT_comp|].
    rewrite poweRM ?lt0r_neq0 ?invr_gt0//=; last first; [apply poweR_ge0
    |apply integral_ge0; [move => ? ?; apply poweR_ge0] | ].
    rewrite gee0_abs ?poweR_ge0 // -poweRrM //=; last first.
      rewrite /poweRrM_def (_ : (r^-1)%:E < 0%R = false); first by apply/implyP.
      rewrite lte_fin invr_lt0; apply /negP.
      by move: (r0); rewrite lte_fin; case : (ltgtP 0%R r).
    rewrite -EFinM divff ?poweRe1 ?poweR_ge0 ?lt0r_neq0//=.
  - move=> _; case: ifPn; last by rewrite mul0e.
    have := phi0 x.
    case : (phi x) => [r||] phix0 ? //=.
    --  case : (ltgtP r 0%R); last first.
    --- move=> ->; rewrite poweR0e // mule0.
        under [X in ess_sup _ X]eq_fun do rewrite mule0 abse0.
        by rewrite ess_sup_cst.
    1,2: move=> r0; rewrite poweR_EFin muleC -ess_sup_pZl //=; last by
        rewrite lt0r powR_ge0 andbT;
        apply /negP; rewrite powR_eq0 (_ : -1 != 0%R) //= andbT => /eqP;
        by move: r0 => /[swap] ->; rewrite ltxx.
    1,2: by under [X in ess_sup _ X]eq_fun do rewrite muleC 
          -( @gee0_abs _ ((r `^ (-1))%:E)) -?poweR_EFin ?poweR_ge0 ?poweR_EFin 
          //= -abse_EFin -abseM.
    -- rewrite poweRyNe //= mule0.
       under [X in ess_sup _ X]eq_fun do rewrite mule0 abse0.
       by rewrite ess_sup_cst.
Qed.

Lemma inv_hpmeanD: 
  forall x, (0 < p) -> 
  'forall_p (fun y => (psi x y) -o (phi x)) = ('exists_p (psi x)) -o (phi x).
Proof.
  move: p => [r||] //= x; rewrite /hpmean //=.
  - case: (ltgtP r%:E 0%:E) => // r0 _; apply /eqP; rewrite eq_sym.