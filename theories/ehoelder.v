(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra unstable boolp interval_inference.
From mathcomp Require Import classical_sets functions cardinality fsbigop reals.
From mathcomp Require Import ereal topology normedtype sequences real_interval.
From mathcomp Require Import esum measure ess_sup_inf lebesgue_measure.
From mathcomp Require Import lebesgue_integral numfun exp convex.

(**md**************************************************************************)
(* # Hoelder's Inequality                                                     *)
(*                                                                            *)
(* This file provides the Lp-norm, Hoelder's inequality and its consequences, *)
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
HB.lock Definition Lnorm {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (\int[mu]_x `|f x| `^ p%:E) `^ p^-1%:E
    (* (mu (f @^-1` (setT `\ 0%R))) when p = 0? *)
  | +oo%E => if mu [set: T] > 0 then ess_sup mu (abse \o f) else 0
  | -oo%E => if mu [set: T] > 0 then ess_inf mu (abse \o f) else 0
  end.
Canonical locked_Lnorm := Unlockable Lnorm.unlock.
Arguments Lnorm {d T R} mu p f.
Local Close Scope ereal_scope.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnorm0 p : 1 <= p -> 'N_p[cst 0] = 0.
Proof.
  rewrite unlock /Lnorm.
  case: p => [r||//].
  - rewrite lee_fin => r1.
    have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
    under eq_integral => x _ do rewrite /= normr0 poweR0e //.
    by rewrite integral0 poweR0e // eqe invr_neq0.
  case: ifPn => // mu0 _; rewrite (ess_sup_ae_cst 0)//.
  by apply: nearW => x; rewrite /= normr0.
Qed.

Lemma Lnorm1 f : 'N_1[f] = \int[mu]_x `|f x|.
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

(*NOTE: cannot be generalized to ereal exponent
cos lack of support for negative basis*)
Lemma Lnorm_cst1 r : ('N_r%:E[cst 1] = (mu setT)`^(r^-1%:E)).
Proof.
rewrite unlock /Lnorm. under eq_integral do rewrite /= normr1 poweR1e.
by rewrite integral_cst// mul1e.
Qed.


End Lnorm_properties.

Section Lnorm_properties.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Lemma Lnormr_ge0 p f : 0 <= 'N_p[f].
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

Lemma Lnormr_eq0_eq0 f p :
  measurable_fun setT f -> (0 < p)%E -> 'N_p[f] = 0 -> f = \0 %[ae mu].
Proof.
rewrite unlock /Lnorm => mf.
case: p => [r||//].
- move=> r0 /eqP; rewrite poweR_eq0y ?lte_fin; 
  last by rewrite integral_ge0 // => x _; rewrite poweR_ge0.
  have igt0 : (0 < (r^-1))%R; first by rewrite invr_gt0.
  move=> /orP [/orP [/orP [/andP [/eqP Ieq0 /eqP invrneq0]|
         /andP [Igt1 /eqP ieqNy]]|
         /andP [Igt0 /eqP ieqy]]| 
         /andP [/eqP Ieqy ilt0]] //=; 
         last by have := lt_trans ilt0 igt0; rewrite ltxx.
  have mp : measurable_fun [set: T] (fun x : T => (`|f x| `^ r%:E)).
  apply (measurableT_comp (measurable_poweR _)) => //; exact: measurableT_comp.
  move: Ieq0. under eq_integral=> x _ do 
    rewrite -( @gee0_abs _ (`|f x| `^ r%:E)) ?poweR_ge0 //.
  move /(ae_eq_integral_abs _ measurableT mp). 
  apply: filterS => x/= /[apply] /eqP; move:r0.
  rewrite poweR_eq0y ?abse_ge0//= !lte_fin eqe (_ : r%:E == -oo = false)//
    (_ : r%:E == +oo = false)//;case: (ltgtP r 0%R) => //=.
  by rewrite !andbF andbT !orbF abse_eq0=> _ _ /eqP.
- case: ifPn => [mu0 _|].
  move=> /abs_sup_eq0_ae_eq/=.
  by apply: filterS => x/= /(_ I) /eqP + _ => /eqP.
  rewrite ltNge => /negbNE mu0 _ _.
  suffices mueq0: mu setT = 0 by exact: ae_eq0.
  by apply/eqP; rewrite eq_le mu0/=.
Qed.

Lemma powR_Lnorm f r : (0 < r)%R ->
  'N_r%:E[f] `^ r%:E = \int[mu]_x (`| f x | `^ r%:E).
Proof. 
rewrite unlock.
have : 0 <= \int[mu]_x ((`| (f x) | `^ r%:E));
  first by apply integral_ge0=> ? _; rewrite poweR_ge0.
case intfx : (\int[mu]_x  (`|(f x)| `^ r%:E)) => [x||] // x0 r0; last first.
- rewrite !poweRyPe ?invr_gt0 ?lte_fin ?invr_gt0 => //.
- rewrite !poweR_EFin; f_equal; rewrite -powRrM mulVf;
  last by rewrite negbT // eq_sym; apply (lt_eqF r0).
  apply powRr1; by move : x0; rewrite lee_fin.
Qed. 

Lemma oppr_Lnorm f p : 'N_p[\- f] = 'N_p[f].
Proof. by rewrite -[RHS]oppe_Lnorm. Qed.

End Lnorm_properties.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `Lnormr_ge0`")]
Notation Lnorm_ge0 := Lnormr_ge0 (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `Lnormr_eq0_eq0`")]
Notation Lnorm_eq0_eq0 := Lnormr_eq0_eq0 (only parsing).

#[global]
Hint Extern 0 (0 <= Lnorm _ _ _) => solve [apply: Lnormr_ge0] : core.

Notation "'N[ mu ]_ p [ f ]" := (Lnorm mu p f) : ereal_scope.

Section lnorm.
Context d {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.
(** lp-norm is just Lp-norm applied to counting *)
Local Notation "'N_ p [ f ]" := (Lnorm counting p f).

Lemma Lnorm_counting p (f : (\bar R)^nat) : (0 < p)%R ->
  'N_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p%:E)) `^ p^-1%:E.
Proof.
by move=> p0;rewrite unlock ge0_integral_count;last by move=>?; rewrite poweR_ge0.
Qed.

End lnorm.

Section conjugate.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Hypothesis p1 : (1 <= p)%E.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition conjugate :=
  match p with
  | r%:E => [get q : R | r^-1 + q^-1 = 1]%:E
  | +oo  => 1
  | -oo  => 0
  end.

Lemma conjugateE :
  conjugate = if p is r%:E then (r * (r-1)^-1)%:E
              else if p == +oo then 1 else 0.
Proof.
rewrite /conjugate.
case: p p1 => [r|//=|//].
rewrite lee_fin => r1.
have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
congr EFin; apply: get_unique.
  by rewrite invf_div mulrBl divff// mul1r addrCA subrr addr0.
move=> /= y ry1.
suff -> : y = (1 - r^-1)^-1.
  by rewrite -(mul1r r^-1) -{1}(divff r0) -mulrBl invf_div.
by rewrite -ry1 -addrAC subrr add0r invrK.
Qed.

End conjugate.

Section hoelder.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (r s : R) (p q : \bar R) (f g : T -> \bar R).

Let measurableT_comp_poweR f p :
  measurable_fun [set: T] f -> measurable_fun setT (fun x => f x `^ p).
Proof. 
move=> ?; apply ( @measurableT_comp _ _ _ _ _ _ ( @poweR (R) ^~ p))=> //=.
exact: measurable_poweR.
Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

Let integrable_poweR f r : (0 < r)%R ->
    measurable_fun [set: T] f -> 'N_r%:E[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ r%:E)).
Proof.
move=> p0 mf foo; apply/integrableP; split.
  apply ( @measurableT_comp _ _ _ _ _ _ ( @poweR (R) ^~ r%:E)) => //=.
  apply: measurable_poweR.
  apply: measurableT_comp => //; apply: measurableT_comp_poweR.
rewrite ltey; apply: contra foo.
rewrite unlock; under eq_integral do rewrite gee0_abs ?poweR_ge0 //.
by move=>/eqP/( @eqy_poweR _ _ r^-1%:E); rewrite lte_fin invr_gt0 => /(_ p0) <-.
Qed.

Let hoelder0 f g p q : measurable_fun setT f -> measurable_fun setT g ->
    (0 < p)%E -> (0 < q)%E -> (p `^-1%:E) + (q`^-1%:E) = 1 ->
  'N_p[f] = 0 -> 'N_1[(f \* g)]  <= 'N_p[f] * 'N_q[g].
Proof.
move=> mf mg p0 q0 pq f0; rewrite f0 mul0e Lnorm1 [leLHS](_ : _ = 0)//.
rewrite (ae_eq_integral (cst 0))=> [|//||//|]; first by rewrite integral0.
- apply: measurableT_comp=> //; exact: emeasurable_funM.
- apply: filterS (Lnormr_eq0_eq0 mf p0 f0) => x /(_ I) + _.
  by move=> -> //= ;apply /eqP; rewrite mul0e abse_eq0.
Qed.

Let normalized p f x := (`|f x|) * ('N_p[f]`^-1%:E).

Let normalized_ge0 p f x : (0 <= normalized p f x).
Proof. by rewrite /normalized mule_ge0// poweR_ge0. Qed.

Let measurable_normalized p f : measurable_fun [set: T] f ->
  measurable_fun [set: T] (normalized p f).
Proof. 
move=> mf; apply: emeasurable_funM=> //; exact: measurableT_comp. Qed.

Let integral_normalized f r : (0 < r)%R -> 0 < 'N_r%:E[f] ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ r%:E)) ->
\int[mu]_x (normalized r%:E f x `^ r%:E) = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ r%:E * ('N_r%:E[f] `^ r%:E)`^ -1%:E)).
apply: eq_integral => t _.
rewrite poweRM ?abse_ge0 ?gt_eqF ?poweR_ge0// poweRAC//.
  by rewrite /poweRrM_def lte_fin (ltNge r) (ltW p0).
  rewrite /poweRrM_def lte_fin (_: (-1 < 0)%R) // fpos //=.
  by rewrite lee_fin (ltW p0) ltNyr ltry !orbT.
have fp0 : 0 < \int[mu]_x (`|f x| `^ r%:E).
  rewrite unlock in fpos.
  apply: gt0_poweR fpos; rewrite ?lte_fin ?invr_gt0 //.
  by apply integral_ge0 => x _;exact: poweR_ge0.
rewrite unlock  -[ X in X `^ (- (1))]poweRrM; last first.
  by rewrite /poweRrM_def lte_fin (ltNge r) (ltW p0).
rewrite -EFinM mulVf ?(poweRe1 (ltW fp0)); last by rewrite negbT ?gt_eqF.
under eq_integral do rewrite muleC.
have : \int[mu]_x (`|f x| `^ r%:E) < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?poweR_ge0//.
have : -oo < \int[mu]_x (`|f x| `^ r%:E).
  apply /(lt_le_trans ltNy0) /integral_ge0 => x _; apply poweR_ge0.
move: fp0; case fr : (\int[mu]_x (`|f x| `^ r%:E)) => // fp0 _ _.
rewrite poweR_EFin integralZl// fr powR_inv1; last by apply /ltW.
apply /eqP; rewrite eqe_pdivrMl ?mule1 // negbT // gt_eqF //. 
Qed.

Lemma hoelder f g p q : measurable_fun setT f -> measurable_fun setT g ->
  (0 < p) -> (0 < q) -> (p`^-1%:E) + (q`^-1%:E) = 1 ->
'N_1[(f \* g)] <= 'N_p[f] * 'N_q[g].
Proof.
move=> mf mg p0 q0 pq.
have [f0|f0] := eqVneq 'N_p[f] 0%E; first exact: hoelder0=> //.
have [g0|g0] := eqVneq 'N_q[g] 0%E.
  rewrite muleC; apply: le_trans;last by apply: hoelder0 => //; rewrite addrC.
  by under eq_Lnorm do rewrite /= muleC.
have {f0}fpos : 0 < 'N_p[f] by rewrite lt0e f0 Lnormr_ge0.
have {g0}gpos : 0 < 'N_q[g] by rewrite lt0e g0 Lnormr_ge0.
have [foo|foo] := eqVneq 'N_p[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q[g] +oo%E; first by rewrite goo gt0_muley ?leey.
have lemu0 :=(measure_ge0 mu [set: T]).
move: p q p0 q0 fpos gpos foo goo pq => [r||] [s||] //=; 
rewrite ?poweRyNe //= ?add0e ?adde0 ?poweR_EFin ?lte_fin => p0 q0 + + + +/eqP; 
rewrite ?(powR_inv1 (ltW p0)) ?(powR_inv1 (ltW q0)) ?eqe ?invr_eq1 
=> fpos gpos foo goo /eqP pq; last first.
by exfalso; rewrite -falseE -( @lt_eqF _ R 0%R 1%R) //; apply /eqP.
1,2: rewrite unlock //=; case : ifPn => //=; last first.
all: try (move:lemu0; case : (ltgtP (mu [set: T]) 0)=>// mu0 _ _; 
  under eq_integral do rewrite poweRe1 ?abse_ge0 //; 
  rewrite ( @integral_abs_eq0 _ _ _ _ [set: T]) // ?mul0e ?mule0 ?poweR0e //; 
    exact /emeasurable_funM=> //). 
all: try (move=> ltmu0; under eq_integral do rewrite poweRe1 ?abse_ge0// ?abseM; 
  rewrite pq invr1 !poweRe1 ?integral_ge0//;
    last by move=> x _;rewrite poweR_ge0).
1: (have : 0  <= ess_sup mu (abse \o  f)); 
    first by apply /ess_sup_gee => //=; exact /aeW => ?; rewrite abse_ge0.
2: rewrite muleC; under eq_integral do rewrite muleC;
   (have : 0  <= ess_sup mu (abse \o  g)); 
    first by apply /ess_sup_gee => //=; exact /aeW => ?; rewrite abse_ge0.
all: try ((case eqef : (ess_sup mu (abse \o  f))=> // [?|]) +
  (case eqef : (ess_sup mu (abse \o  g))=> // [?|]) => ?; 
    last by (move: pq gpos) + (move: pq fpos) => ->; rewrite Lnorm1 => ?; 
      rewrite gt0_mulye ?leey //; by under eq_integral do rewrite poweRe1 //).
all: try ( rewrite -integralZl//; 
  last by apply: integrable_poweR=>//=;rewrite -pq).
all: try (under [X in _ <= X]eq_integral do rewrite poweRe1 //; 
  apply /ae_ge0_le_integral => //=;
  [apply/emeasurable_funM/measurableT_comp=>//; 
    apply/measurableT_comp=>//
  |by move=> x _; rewrite mule_ge0 
  |apply/emeasurable_funM=> //; apply /measurableT_comp=> // 
  |(apply:filterS( @ess_sup_ge _ _ _ mu (abse \o f)))
    + (apply:filterS( @ess_sup_ge _ _ _ mu (abse \o g)))=>x/=le_absf_essabsf _;
    by rewrite -eqef lee_pmul //]).  
pose F := normalized r%:E f; pose G := normalized s%:E g.
rewrite [leLHS](_:_= 'N_1[(F \* G)] * 'N_r%:E[f] * 'N_s%:E[g]);last first.
  rewrite !Lnorm1; under [in RHS]eq_integral.
    move=> x _; rewrite /F /G /normalized/=.
    rewrite gee0_abs; last by rewrite !mule_ge0 ?abse_ge0 ?poweR_ge0 //.
    rewrite muleACA -abseM; over.
  rewrite ge0_integralZr//; last 2 first.
  - apply: measurableT_comp => //; exact: emeasurable_funM.
  - by rewrite mule_ge0 ?poweR_ge0 //.
  rewrite -muleA -muleA [X in _ * X](_ : _ = 1) ?mule1// muleACA.
  move: fpos gpos foo goo; case: ('N_ r%:E [f]); 
      case: ('N_ s%:E [g]) => // a b + + _ _. 
    rewrite !lte_fin !poweR_EFin -EFinM=> bpos apos;f_equal.
    rewrite !powR_inv1; try by rewrite ?le0r ?bpos ?apos orbC.
    by rewrite !mulVf ?mul1r ?gt_eqF.
  rewrite -(mul1e ('N_r%:E[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnormr_ge0//.
  rewrite [leRHS](_ : _ = 
  \int[mu]_x ((F x `^ r%:E)*(r^-1%:E)  + (G x `^ s%:E)*(s^-1%:E))); last first.
  rewrite ge0_integralD//; last 4 first.
  - by move=> x _;rewrite mule_ge0 ?poweR_ge0 ?lee_fin ?invr_ge0 ?ltW.
  1,3: apply /emeasurable_funM => //;
    by apply /measurableT_comp_poweR /measurable_normalized.
  - by move=> x _; rewrite mule_ge0 ?poweR_ge0 ?ltW ?lte_fin ?invr_gt0.
  rewrite !ge0_integralZr//; last 3 first.
  all: try by apply /measurableT_comp_poweR; exact: measurable_normalized.
  all: try by move=> x _; rewrite poweR_ge0.
  all: try by rewrite lee_fin invr_ge0 ltW.
  repeat (rewrite integral_normalized//; last exact:integrable_poweR).
  by rewrite !mul1e -EFinD;f_equal; apply esym.
rewrite Lnorm1 ae_ge0_le_integral//.
  - apply: measurableT_comp => //.
    by apply: emeasurable_funM=> //; exact: measurable_normalized.
  - move=> x _; rewrite // /F /G /normalized.
    have := le_lt_trans leNy0 fpos; have := le_lt_trans leNy0 gpos.
    move: foo goo fpos gpos; case If : ('N_ r%:E [f]); 
      case Ig : ('N_ s%:E [g]) => // foo goo fpos gpos _ _.
        by rewrite ?adde_ge0 ?mule_ge0 ?poweR_ge0 ?ltW ?lte_fin ?invr_gt0.
  - apply /emeasurable_funD; apply /emeasurable_funM => //;
      by apply /measurableT_comp_poweR; exact: measurable_normalized.
apply /aeW => x _; rewrite gee0_abs; last by rewrite mule_ge0 // normalized_ge0.
by rewrite conjugate_poweR// normalized_ge0. 
Qed.

End hoelder.

Section hoelder2.
Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma hoelder2 (a1 a2 b1 b2 : \bar R) (p q : R) :
  0 <= a1 -> 0 <= a2 -> 0 <= b1 -> 0 <= b2 ->
  0 < p%:E -> 0 < q%:E -> ((p%:E`^-1%:E) + q%:E`^-1%:E) = 1 ->
  a1 * b1 + a2 * b2 <= ((a1 `^ p%:E + a2 `^ p%:E) `^ (p%:E`^-1%:E)) *
                       ((b1 `^ q%:E + b2 `^ q%:E) `^ (q%:E`^-1%:E)).
Proof.
move=> a10 a20 b10 b20 p0 q0 pq.
- pose f a b n : \bar R := match n with 0%nat => a | 1%nat => b | _ => 0 end.
  have mf a b : measurable_fun setT (f a b) by [].
  have := hoelder counting (mf a1 a2) (mf b1 b2) p0 q0 pq.
  rewrite !Lnorm_counting//.
  rewrite (nneseries_split 0 2); last by move=> k; rewrite poweRe1.
  rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
    by move=> [//|] [//|n _]; rewrite /f /= mulr0 normr0 poweR0e.
  rewrite big_mkord 2!big_ord_recr/= big_ord0 add0e.
  rewrite !poweRe1 //.
  rewrite (nneseries_split 0 2); last by move=> k; rewrite poweR_ge0.
  rewrite ereal_series_cond eseries0 ?adde0; last first.
    by move=> [//|] [//|n _]; rewrite /f /= poweR_EFin => _;
      rewrite normr0 powR0// gt_eqF.
  rewrite big_mkord 2!big_ord_recr /= big_ord0 add0e.
  rewrite (nneseries_split 0 2); last by move=> k; rewrite poweR_ge0.
  rewrite ereal_series_cond eseries0 ?adde0; last first.
    by move=> [//|] [//|n _]; rewrite /f /= normr0 poweR0e ?gt_eqF.
  rewrite big_mkord 2!big_ord_recr /= big_ord0 add0e.
  rewrite invr1 poweRe1; last by rewrite adde_ge0 //.
  do 2 (rewrite gee0_abs; last by rewrite mule_ge0).
  do 4 (rewrite gee0_abs; last by []).
  by rewrite !poweR_EFin !powR_inv1 //= -?lee_fin ?ltW.
Qed.

End hoelder2.

Section convex_powR.
Context {R : realType}.
Local Open Scope ring_scope.

Lemma convex_powR p : 1 <= p ->
  convex_function `[0, +oo[%classic (@powR R ^~ p).
Proof.
move=> p1 t x y /[!inE] /= /[!in_itv] /= /[!andbT] x_ge0 y_ge0.
have p0 : 0 < p by rewrite (lt_le_trans _ p1).
rewrite !convRE; set w1 := `1-(t%:inum); set w2 := t%:inum.
have [->|w10] := eqVneq w1 0.
  rewrite !mul0r !add0r; have [->|w20] := eqVneq w2 0.
    by rewrite !mul0r powR0// gt_eqF.
  by rewrite ge1r_powRZ// /w2 lt_neqAle eq_sym w20/=; apply/andP.
have [->|w20] := eqVneq w2 0.
  by rewrite !mul0r !addr0 ge1r_powRZ// onem_le1// andbT lt0r w10 onem_ge0.
have [->|p_neq1] := eqVneq p 1.
  by rewrite !powRr1// addr_ge0// mulr_ge0// /w2 ?onem_ge0.
have {p_neq1} {}p1 : 1 < p by rewrite lt_neqAle eq_sym p_neq1.
pose q := p / (p - 1).
have q1 : 1 <= q by rewrite /q ler_pdivlMr// ?mul1r ?gerBl// subr_gt0.
have q0 : 0 < q by rewrite (lt_le_trans _ q1).
have pq1 : p^-1 + q^-1 = 1.
  rewrite /q invf_div -{1}(div1r p) -mulrDl addrCA subrr addr0.
  by rewrite mulfV// gt_eqF.
rewrite -(@powRr1 _ (w1 * x `^ p + w2 * y `^ p)); last first.
  by rewrite addr_ge0// mulr_ge0// ?powR_ge0// /w2 ?onem_ge0// itv_ge0.
have -> : 1 = p^-1 * p by rewrite mulVf ?gt_eqF.
rewrite powRrM (ge0_ler_powR (le_trans _ (ltW p1)))//.
- by rewrite nnegrE addr_ge0// mulr_ge0 /w2 ?onem_ge0.
- by rewrite nnegrE powR_ge0.
have -> : w1 * x + w2 * y = w1 `^ (p^-1) * w1 `^ (q^-1) * x +
                            w2 `^ (p^-1) * w2 `^ (q^-1) * y.
  rewrite -!powRD pq1; [|exact/implyP..].
  by rewrite !powRr1// /w2 ?onem_ge0.
apply: (@le_trans _ _ ((w1 * x `^ p + w2 * y `^ p) `^ (p^-1) *
                       (w1 + w2) `^ q^-1)).
  pose a1 := w1 `^ p^-1 * x. pose a2 := w2 `^ p^-1 * y.
  pose b1 := w1 `^ q^-1. pose b2 := w2 `^ q^-1.
  have : a1 * b1 + a2 * b2 <= (a1 `^ p + a2 `^ p) `^ p^-1 *
                              (b1 `^ q + b2 `^ q) `^ q^-1.
    by apply: hoelder2 => //; rewrite ?mulr_ge0 ?powR_ge0.
  rewrite ?powRM ?powR_ge0 -?powRrM ?mulVf ?powRr1 ?gt_eqF ?onem_ge0/w2//.
  by rewrite mulrAC (mulrAC _ y) => /le_trans; exact.
by rewrite {2}/w1 {2}/w2 subrK powR1 mulr1.
Qed.

End convex_powR.

Section minkowski.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Implicit Types (f g : T -> R) (p : R).

Let convex_powR_abs_half f g p x : 1 <= p ->
  `| 2^-1 * f x + 2^-1 * g x | `^ p <=
   2^-1 * `| f x | `^ p + 2^-1 * `| g x | `^ p.
Proof.
move=> p1; rewrite (@le_trans _ _ ((2^-1 * `| f x | + 2^-1 * `| g x |) `^ p))//.
  rewrite ge0_ler_powR ?nnegrE ?(le_trans _ p1)//.
  by rewrite (le_trans (ler_normD _ _))// 2!normrM ger0_norm.
rewrite {1 3}(_ : 2^-1 = 1 - 2^-1); last by rewrite {2}(splitr 1) div1r addrK.
rewrite (@convex_powR _ _ _ (Itv01 _ _))// ?inE/= ?in_itv/= ?normr_ge0 ?invr_ge0//.
by rewrite invf_le1 ?ler1n.
Qed.

Let measurableT_comp_poweR f p :
  measurable_fun setT f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)). Qed.

Local Notation "'N_ p [ f ]" := (Lnorm mu p (EFin \o f)).
Local Open Scope ereal_scope.

Let minkowski1 f g p : measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  'N_1[(f \+ g)%R] <= 'N_1[f] + 'N_1[g].
Proof.
move=> mf mg.
rewrite !Lnorm1 -ge0_integralD//=; [|by do 2 apply: measurableT_comp..].
rewrite ge0_le_integral//.
- by do 2 apply: measurableT_comp => //; exact: measurable_funD.
- by move=> x _; rewrite adde_ge0.
- by apply/measurableT_comp/measurable_funD; exact/measurableT_comp.
- by move=> x _; rewrite lee_fin ler_normD.
Qed.

Let minkowski_lty f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] < +oo -> 'N_p%:E[g] < +oo -> 'N_p%:E[(f \+ g)%R] < +oo.
Proof.
move=> mf mg p1 Nfoo Ngoo.
have p0 : p != 0%R by rewrite gt_eqF// (lt_le_trans _ p1).
have h x : (`| f x + g x | `^ p <=
            2 `^ (p - 1) * (`| f x | `^ p + `| g x | `^ p))%R.
  have := convex_powR_abs_half (fun x => 2 * f x)%R (fun x => 2 * g x)%R x p1.
  rewrite !normrM (@ger0_norm _ 2)// !mulrA mulVf// !mul1r => /le_trans; apply.
  rewrite !powRM// !mulrA -powR_inv1// -powRD ?pnatr_eq0 ?implybT//.
  by rewrite (addrC _ p) -mulrDr.
rewrite unlock poweR_lty// ?ltNyr ?ltry //=.
pose x := \int[mu]_x (2 `^ (p - 1) * (`|f x| `^ p + `|g x| `^ p))%:E.
apply: (@le_lt_trans _ _ x).
  rewrite ge0_le_integral//=; first by move=> x0 _; rewrite poweR_ge0.
  under eq_fun do rewrite poweR_EFin.
  - apply/measurable_EFinP/measurableT_comp_poweR/measurableT_comp => //.
    exact: measurable_funD.
  - by apply/measurable_EFinP/measurable_funM/measurable_funD => //;
      exact/measurableT_comp_poweR/measurableT_comp.
  - move=> ? _. by rewrite poweR_EFin lee_fin.
rewrite {}/x; under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin ?powR_ge0//; last first.
  by apply/measurable_EFinP/measurable_funD => //;
    exact/measurableT_comp_poweR/measurableT_comp.
rewrite lte_mul_pinfty ?lee_fin ?powR_ge0//.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 2 first.
  - exact/measurable_EFinP/measurableT_comp_poweR/measurableT_comp.
  - exact/measurable_EFinP/measurableT_comp_poweR/measurableT_comp.
rewrite lte_add_pinfty// -powR_Lnorm ?poweR_lty ?ltNyr ?ltry//.
all: apply /(lt_le_trans ltr01 p1).
Qed.

Lemma minkowski_EFin f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[(f \+ g)%R] <= 'N_p%:E[f] + 'N_p%:E[g].
Proof.
move=> mf mg; rewrite le_eqVlt => /predU1P[<-|p1]; first exact: minkowski1.
have [->|Nfoo] := eqVneq 'N_p%:E[f] +oo.
  by rewrite addye ?leey// -ltNye (lt_le_trans _ (Lnormr_ge0 _ _ _)).
have [->|Ngoo] := eqVneq 'N_p%:E[g] +oo.
  by rewrite addey ?leey// -ltNye (lt_le_trans _ (Lnormr_ge0 _ _ _)).
have Nfgoo : 'N_p%:E[(f \+ g)%R] < +oo.
  by rewrite minkowski_lty// ?ltW// ltey; [exact: Nfoo|exact: Ngoo].
suff : 'N_p%:E[(f \+ g)%R] `^ p%:E <= ('N_p%:E[f] + 'N_p%:E[g]) *
    'N_p%:E[(f \+ g)%R] `^ p%:E * (fine 'N_p%:E[(f \+ g)%R])^-1%:E.
  have [-> _|Nfg0] := eqVneq 'N_p%:E[(f \+ g)%R] 0.
    by rewrite adde_ge0 ?Lnormr_ge0.
  rewrite lee_pdivlMr ?fine_gt0// ?lt0e ?Nfg0 ?Lnormr_ge0//.
  rewrite -{1}(@fineK _ ('N_p%:E[(f \+ g)%R] `^ p%:E)); last first.
    by rewrite fin_num_poweR// ge0_fin_numE// Lnormr_ge0.
  rewrite -(invrK (fine _)) lee_pdivrMl; last first.
    rewrite invr_gt0 fine_gt0// poweR_lty ?ltNyr ?ltry ?andbT ?poweR_gt0 //=.
    by rewrite lt0e Nfg0 Lnormr_ge0.
  rewrite fineK ?ge0_fin_numE ?Lnormr_ge0// => /le_trans; apply.
  rewrite lee_pdivrMl; last first.
    by rewrite fine_gt0// poweR_lty// ?ltNyr ?ltry ?andbT // poweR_gt0// lt0e 
      Nfg0 Lnormr_ge0.
  by rewrite fineK// 1?muleC// fin_num_poweR// ge0_fin_numE ?Lnormr_ge0.
have p0 : (0 < p)%R by exact: (lt_trans _ p1).
rewrite powR_Lnorm ?gt_eqF//.
under eq_integral => x _ do rewrite -mulr_powRB1//.
apply: (@le_trans _ _
    (\int[mu]_x ((`|f x| + `|g x|) * `|f x + g x| `^ (p - 1))%:E)).
  rewrite ge0_le_integral//.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact/measurableT_comp/measurable_funD.
    exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
  - apply/measurableT_comp => //; apply: measurable_funM.
      by apply/measurable_funD => //; exact: measurableT_comp.
    exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
  - by move=> ? _; rewrite lee_fin ler_wpM2r// ?powR_ge0// ler_normD.
under eq_integral=> ? _ do rewrite mulrDl EFinD.
rewrite ge0_integralD//; last 2 first.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
  - apply: measurableT_comp => //; apply: measurable_funM.
      exact: measurableT_comp.
    exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
rewrite [leRHS](_ : _ = ('N_p%:E[f] + 'N_p%:E[g]) *
    (\int[mu]_x (`|f x + g x| `^ p)%:E) `^ `1-(p^-1)%:E).
  rewrite muleDl; last 2 first.
    - rewrite fin_num_poweR// -powR_Lnorm ?gt_eqF// fin_num_poweR//.
      by rewrite ge0_fin_numE ?Lnormr_ge0.
    - by rewrite ge0_adde_def// inE Lnormr_ge0.
  apply: leeD.
  - pose h := (@powR R ^~ (p - 1) \o normr \o (f \+ g))%R; pose i := (f \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]%R); last first.
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM (ger0_norm (powR_ge0 _ _)).
    rewrite [X in _ * X](_ : _ = 'N_(p / (p - 1))%:E[h]); last first.
      rewrite unlock.
      rewrite onemV ?gt_eqF// invf_div; apply: congr2; last by [].
      apply: eq_integral => x _; rewrite abse_EFin poweR_EFin; congr EFin.
      rewrite norm_powR// normr_id -powRrM mulrCA divff ?mulr1//.
      by rewrite subr_eq0 gt_eqF.
    apply: (@hoelder _ _ _ _ _ _ p (p / (p - 1))) => //.
    + exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
    + by rewrite divr_gt0// subr_gt0.
    + by rewrite invf_div -onemV ?gt_eqF// addrCA subrr addr0.
  - pose h := (fun x => `|f x + g x| `^ (p - 1))%R; pose i := (g \* h)%R.
    rewrite [leLHS](_ : _ = 'N_1[i]); last first.
      rewrite Lnorm1; apply: eq_integral => x _ /=.
      by rewrite normrM norm_powR// normr_id.
    rewrite [X in _ * X](_ : _ = 'N_((1 - p^-1)^-1)%:E[h])//; last first.
      rewrite unlock.
      apply: congr2; last by rewrite invrK.
      apply: eq_integral => x _; rewrite abse_EFin poweR_EFin; congr EFin.
      rewrite -/(onem p^-1) onemV ?gt_eqF// norm_powR// normr_id -powRrM.
      by rewrite invf_div mulrCA divff ?subr_eq0 ?gt_eqF// ?mulr1.
    apply: (le_trans (@hoelder _ _ _ _ _ _ p (1 - p^-1)^-1 _ _ _ _ _)) => //.
    + exact/measurableT_comp_poweR/measurableT_comp/measurable_funD.
    + by rewrite invr_gt0 onem_gt0// invf_lt1.
    + by rewrite invrK addrCA subrr addr0.
rewrite -muleA; congr (_ * _).
under [X in X * _]eq_integral=> x _ do rewrite mulr_powRB1 ?subr_gt0//.
have Ifin : \int[mu]_x  (`|(f x + g x)%E| `^ p)%:E  \is a fin_num.
  rewrite ge0_fin_numE //= -powR_Lnorm ?poweR_ge0 //=; apply /poweR_lty => //=.
  by rewrite ?ltNyr ?ltry.
rewrite EFinD poweRD. 
rewrite poweRe1; last by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
congr (_ * _); rewrite -mulN1r EFinM mulN1e poweRN.
rewrite unlock fine_poweR; under eq_integral do rewrite abse_EFin poweR_EFin.
by rewrite /fine //=.
rewrite -powR_Lnorm ?gt_eqF//; apply /(lt_le_trans ltNy0)/poweR_ge0.
by rewrite Ifin.
all: rewrite ?ge0_fin_numE ?ltNyr ?ltry ?lee_fin ?invr_ge0 ?ltW//=.
move: Ifin; rewrite -powR_Lnorm //. rewrite fin_numE.
case: ('N_p%:E [(f \+ g)] `^ p%:E) => //= r _.
apply /implyP => /eqP /subr0_eq /eqP; rewrite eq_sym invr_eq1 => /eqP.
move: p1 => /[swap] ->; by rewrite ltxx.
Qed.

Lemma lerB_DLnorm f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] <= 'N_p%:E[f \+ g] + 'N_p%:E[g].
Proof.
move=> mf mg p1.
rewrite (_ : f = ((f \+ g) \+ (-%R \o g))%R); last first.
  by apply: funext => x /=; rewrite -addrA subrr addr0.
rewrite [X in _ <= 'N__[X] + _](_ : _ = (f \+ g)%R); last first.
  by apply: funext => x /=; rewrite -addrA [X in _ + _ + X]addrC subrr addr0.
rewrite (_ : 'N__[g] = 'N_p%:E[-%R \o g]); last by rewrite oppr_Lnorm.
by apply: minkowski_EFin => //;
  [exact: measurable_funD|exact: measurableT_comp].
Qed.

Lemma lerB_LnormD f g p :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> (1 <= p)%R ->
  'N_p%:E[f] - 'N_p%:E[g] <= 'N_p%:E[f \+ g].
Proof.
move=> mf mg p1.
set rhs := (leRHS); have [?|] := boolP (rhs \is a fin_num).
  by rewrite lee_subel_addr//; exact: lerB_DLnorm.
rewrite fin_numEn => /orP[|/eqP ->]; last by rewrite leey.
by rewrite gt_eqF// (lt_le_trans _ (Lnormr_ge0 _ _ _)).
Qed.

(* TODO: rename to minkowski after version 1.12.0 *)
Lemma eminkowski f g (p : \bar R) :
  measurable_fun [set: T] f -> measurable_fun [set: T] g -> 1 <= p ->
  'N_p[(f \+ g)%R] <= 'N_p[f] + 'N_p[g].
Proof.
case: p => //[r|]; first exact: minkowski_EFin.
move=> mf mg _; rewrite unlock /Lnorm.
case: ifPn => mugt0; last by rewrite adde0 lexx.
exact: ess_sup_normD.
Qed.

End minkowski.
#[deprecated(since="mathcomp-analysis 1.10.0",
  note="use `minkowski_EFin` or `eminkowski` instead")]
Notation minkowski := minkowski_EFin (only parsing).

Definition finite_norm d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) :=
  ('N[ mu ]_p [ EFin \o f ] < +oo)%E.

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) (f : T -> R)
  of @MeasurableFun d _ T R f := {
  lfuny : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of @MeasurableFun d _ T R f & isLfun d T R mu p p1 f}.

Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) => solve [apply: lfuny] : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

HB.instance Definition _ := gen_eqMixin (LfunType mu p1).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p1).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Definition Lequiv (f g : LfunType mu p1) := `[< f = g %[ae mu] >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP/ae_eq_sym.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_eq_trans gf fh).
Qed.

Canonical Lequiv_canonical :=
  EquivRel Lequiv Lequiv_refl Lequiv_sym Lequiv_trans.

Local Open Scope quotient_scope.

Definition LspaceType := {eq_quot Lequiv}.
HB.instance Definition _ := Choice.on LspaceType.
HB.instance Definition _ := EqQuotient.on LspaceType.

Lemma LequivP (f g : LfunType mu p1) :
  reflect (f = g %[ae mu]) (f == g %[mod LspaceType]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

Record LType := MemLType { Lfun_class : LspaceType }.
Coercion LfunType_of_LType (f : LType) : LfunType mu p1 :=
  repr (Lfun_class f).

End Lequiv.

Section mfun_extra.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}).

Lemma mfunP (f : {mfun T >-> R}) : (f : T -> R) \in mfun.
Proof. exact: valP. Qed.

Import numFieldNormedType.Exports.

Lemma mfun_scaler_closed : scaler_closed (@mfun _ _ T R).
Proof. by move=> a/= f; rewrite !inE; exact: measurable_funM. Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ (@mfun _ _ T R)
  mfun_scaler_closed.

HB.instance Definition _ := [SubZmodule_isSubLmodule of {mfun T >-> R} by <:].

End mfun_extra.

Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finlfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition lfun : {pred _ -> _} := [predI @mfun _ _ T R & finlfun].
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
Lemma sub_lfun_mfun : {subset lfun <= mfun}.
Proof. by move=> x /andP[]. Qed.
Lemma sub_lfun_finlfun : {subset lfun <= finlfun}.
Proof. by move=> x /andP[]. Qed.

End lfun_pred.

Reserved Notation "[ 'lfun' 'of' f ]"
  (at level 0, format "[ 'lfun'  'of'  f ]").
Notation "[ 'lfun' 'of' f ]" := [the LfunType _ _ of f] : form_scope.

Section lfun.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).
Notation lfun := (@lfun _ T R mu p).

Section Sub.
Context (f : T -> R) (fP : f \in lfun).
Definition lfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ T R f (set_mem (sub_lfun_mfun fP)).
#[local] HB.instance Definition _ := lfun_Sub1_subproof.

Definition lfun_Sub2_subproof :=
  @isLfun.Build d T R mu p p1 f (set_mem (sub_lfun_finlfun fP)).
#[local] HB.instance Definition _ := lfun_Sub2_subproof.
Definition lfun_Sub := [lfun of f].
End Sub.

Lemma lfun_rect (K : LfunType mu p1 -> Type) :
  (forall f (Pf : f \in lfun), K (lfun_Sub Pf)) -> forall u, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]].
have Pf : f \in lfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_lfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_lfun_finlfun Pf) by [].
exact: Ksub.
Qed.

Lemma lfun_valP f (Pf : f \in lfun) : lfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ :=
  isSub.Build _ _ (LfunType mu p1) lfun_rect lfun_valP.

Lemma lfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0// ltry. Qed.

HB.instance Definition _ := @isLfun.Build d T R mu p p1 (cst 0) lfuny0.

Lemma lfunP (f : LfunType mu p1) : (f : T -> R) \in lfun.
Proof. exact: valP. Qed.

Lemma lfun_oppr_closed : oppr_closed lfun.
Proof.
move=> f /andP[mf /[!inE] lf].
by rewrite rpredN/= mf/= inE/= /finite_norm oppr_Lnorm.
Qed.

HB.instance Definition _ := GRing.isOppClosed.Build _ lfun
  lfun_oppr_closed.

(* NB: not used directly by HB.instance *)
Lemma lfun_addr_closed : addr_closed lfun.
Proof.
split.
  by rewrite inE rpred0/= inE/= /finite_norm/= Lnorm0.
move=> f g /andP[mf /[!inE]/= lf] /andP[mg /[!inE]/= lg].
rewrite rpredD//= inE/=.
rewrite /finite_norm.
rewrite (le_lt_trans (@eminkowski _ _ _ mu f g p _ _ _))//.
- by rewrite inE in mf.
- by rewrite inE in mg.
- by rewrite lte_add_pinfty.
Qed.

Import numFieldNormedType.Exports.

Lemma LnormZ (f : LfunType mu p1) a :
  ('N[mu]_p[EFin \o (a \*: f)] = `|a|%:E * 'N[mu]_p[EFin \o f])%E.
Proof.
rewrite unlock /Lnorm.
case: p p1 f => //[r r1 f|? f].
- under eq_integral do 
  rewrite /= -mulr_algl scaler1 normrM poweR_EFin powRM ?EFinM//.
  rewrite integralZl//; last first.
    apply/integrableP; split.
      apply: measurableT_comp => //.
      apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
      exact: measurableT_comp.
    apply: (@lty_poweRy _ _ r^-1%:E).
      by rewrite lte_fin invr_gt0 ?(lt_le_trans ltr01).
    rewrite [ltLHS](_ : _ = 'N[mu]_r%:E[EFin \o f]%E); first exact: (lfuny r1 f).
    rewrite unlock /Lnorm.
    by under eq_integral do rewrite gee0_abs ?lee_fin ?powR_ge0 -?poweR_EFin//.
  rewrite poweRM ?integral_ge0 => //.
  rewrite poweR_EFin -powRrM mulfV ?gt_eqF ?(lt_le_trans ltr01)// powRr1 //=.
    by under eq_integral do rewrite -poweR_EFin.
  by rewrite gt_eqF// invr_gt0; apply /(lt_le_trans ltr01).
- case: ifPn => mu0; last by rewrite mule0.
  rewrite -ess_supZl//; apply/eq_ess_sup/nearW => t /=.
  by rewrite normrZ EFinM.
Qed.

Lemma lfun_submod_closed : submod_closed lfun.
Proof.
split.
  by rewrite -[0]/(cst 0); exact: lfunP.
move=> a/= f g fP gP.
rewrite -[f]lfun_valP -[g]lfun_valP.
move: (lfun_Sub _) (lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=; apply: (le_lt_trans (eminkowski _ _ _ _)) => //.
- suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
- rewrite lte_add_pinfty//; last exact: lfuny.
  by rewrite LnormZ lte_mul_pinfty// ?lee_fin//; exact: lfuny.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ lfun
  lfun_submod_closed.

HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End lfun.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (p : \bar R) (p1 : (1 <= p)%E).

(* TODO: 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Let nm f := fine ('N[mu]_p[EFin \o f]).

Lemma finite_norm_fine (f : ty) : (nm f)%:E = 'N[mu]_p[EFin \o f]%E.
Proof.
rewrite /nm fineK// fin_numElt (lt_le_trans ltNy0) ?Lnormr_ge0//=.
exact: lfuny.
Qed.

Lemma ler_LnormD (f g : ty) : nm (f + g) <= nm f + nm g.
Proof. by rewrite -lee_fin EFinD !finite_norm_fine eminkowski. Qed.

Lemma LnormrN (f : ty) : nm (\-f) = nm f.
Proof. by rewrite /nm oppr_Lnorm. Qed.

Lemma Lnormr_natmul (f : ty) k : nm (f *+ k) = nm f *+ k.
Proof.
apply/EFin_inj; rewrite finite_norm_fine -scaler_nat LnormZ normr_nat.
by rewrite -[in RHS]mulr_natl EFinM finite_norm_fine.
Qed.

(* TODO : fix the definition *)
(* waiting for MathComp 2.4.0
HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (LfunType mu p1)
     nm ler_Lnorm_add Lnorm_natmul LnormN.
*)

(* TODO: add equivalent of mx_normZ and HB instance *)

Lemma fine_Lnormr_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
move=> /eqP; rewrite -eqe => /eqP.
rewrite finite_norm_fine => /Lnormr_eq0_eq0.
by apply; rewrite ?(lt_le_trans _ p1).
Qed.

End Lspace_norm.

Section Lspace.
  Context d (T : measurableType d) (R : realType).
  Variable mu : {measure set T -> \bar R}.
  
  Definition Lspace p (p1 : (1 <= p)%E) := [set: LType mu p1].
  Arguments Lspace : clear implicits.
  
  Definition LType1 := LType mu (@lexx _ _ 1%E).
  
  Definition LType2 := LType mu (lee1n 2).
  
  Lemma lfun_integrable (f : T -> R) r :
    1 <= r -> f \in lfun mu r%:E ->
    mu.-integrable setT (fun x => (`|f x| `^ r)%:E).
  Proof.
  rewrite inE => r0 /andP[/[!inE]/= mf] lpf.
  apply/integrableP; split => //.
    apply: measurableT_comp => //.
    apply: (measurableT_comp (measurable_powR _)) => //.
    exact: measurableT_comp.
  move: lpf=> /(@poweR_lty _ _ r%:E).
  rewrite powR_Lnorm// ?gt_eqF// ?(lt_le_trans ltr01)//.
  under eq_integral=> x _ do 
  rewrite -(@gee0_abs _ (`|f x| `^ r)%:E) ?powR_ge0//= -abse_EFin.
  by move=> -> //=; rewrite ltNyr ltry.
Qed.

Lemma lfun1_integrable (f : T -> R) :
  f \in lfun mu 1 <-> mu.-integrable setT (EFin \o f).
Proof.
split.
  move=> /[dup] lf /lfun_integrable => /(_ (lexx _)).
  under eq_fun => x do rewrite powRr1//.
  move/integrableP => [mf fley].
  apply/integrableP; split.
    move: lf; rewrite inE => /andP[/[!inE]/= {}mf _].
    exact: measurableT_comp.
  rewrite (le_lt_trans _ fley)//=.
  by under [leRHS]eq_integral => x _ do rewrite normr_id.
move/integrableP => [mF iF].
rewrite inE; apply/andP; split; rewrite inE/=.
  exact/measurable_EFinP.
by rewrite /finite_norm Lnorm1.
Qed.

Lemma lfun2_integrable_sqr (f : T -> R) :
  f \in lfun mu 2%:E -> mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
rewrite inE => /andP[mf]; rewrite inE/= => l2f.
move: mf; rewrite inE/= => mf.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_funX.
rewrite (@lty_poweRy _ _ 2^-1%:E)//.
rewrite (le_lt_trans _ l2f)//.
rewrite unlock.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= leey integral_ge0// => x _.
- by rewrite in_itv/= leey integral_ge0//= => x _;rewrite poweR_ge0.
- rewrite ge0_le_integral//.
  + apply: measurableT_comp => //; apply/measurable_EFinP.
    exact: measurable_funX.
  + by move=> x _; rewrite poweR_EFin lee_fin powR_ge0.
  + under eq_fun=> x do rewrite poweR_EFin; apply/measurable_EFinP.
    apply/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R) => //.
    exact/measurableT_comp.
  + by move=> t _/=; rewrite poweR_EFin lee_fin normrX powR_mulrn.
Qed.

Lemma lfun2M2_1 (f g : T -> R) : f \in lfun mu 2%:E -> g \in lfun mu 2%:E ->
  f \* g \in lfun mu 1.
Proof.
move=> l2f l2g.
move: (l2f) (l2g) => /[!inE] /andP[/[!inE]/= mf _] /andP[/[!inE]/= mg _].
apply/andP; split.
  by rewrite inE/=; apply: measurable_funM.
rewrite !inE/= /finite_norm.
apply: le_lt_trans.
  by apply: (@hoelder _ _ _ _ _ _ 2 2) => //; rewrite [RHS]splitr !div1r.
rewrite lte_mul_pinfty// ?ge0_fin_numE ?Lnormr_ge0//.
by move: l2f; rewrite inE => /andP[_]; rewrite inE/=.
by move: l2g; rewrite inE => /andP[_]; rewrite inE/=.
Qed.

Lemma lfunp_scale (f : T -> R) a r :
  1 <= r -> f \in lfun mu r%:E -> a \o* f \in lfun mu r%:E.
Proof.
move=> r1 /[dup] lf lpf.
rewrite inE; apply/andP; split.
  move: lf; rewrite inE => /andP[/[!inE]/= lf _].
  exact: measurable_funM.
rewrite !inE/= /finite_norm unlock /Lnorm.
rewrite poweR_lty//= ?ltNyr ?ltry //.
under eq_integral => x _ do rewrite poweR_EFin normrM powRM// EFinM.
rewrite integralZr// ?lfun_integrable//.
rewrite muleC lte_mul_pinfty// ?lee_fin ?powR_ge0//.
move: lpf => /(lfun_integrable r1) /integrableP[_].
under eq_integral => x _ do rewrite gee0_abs ?lee_fin ?powR_ge0//.
by [].
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

Section Lspace_finite_measure.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.

Lemma lfun_cst c r : cst c \in lfun mu r%:E.
Proof.
rewrite inE; apply/andP; split; rewrite inE//= /finite_norm unlock/Lnorm 
  poweR_lty// ?ltNyr ?ltry //=.
under eq_integral => x _/= do rewrite poweR_EFin (_ : `|c| `^ r = cst (`|c| `^ r) x)//.
have /integrableP[_/=] := finite_measure_integrable_cst mu (`|c| `^ r).
under eq_integral => x _ do rewrite ger0_norm ?powR_ge0//.
by [].
Qed.

End Lspace_finite_measure.

Section lfun_inclusion.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma lfun_inclusion (p q : \bar R) : forall (p1 : 1 <= p) (q1 : 1 <= q),
  p <= q -> {subset lfun mu q <= lfun mu p}.
Proof.
have ? : forall x:R, -oo < x%:E < +oo; first by move=> ?; rewrite ltNyr ltry.
have := measure_ge0 mu [set: T].
rewrite le_eqVlt => /predU1P[mu0 p1 q1 pq f +|mu_pos].
  rewrite inE => /andP[/[1!inE]/= mf _].
  rewrite inE; apply/andP; split; rewrite inE//=.
  rewrite /finite_norm unlock /Lnorm.
  move: p p1 {pq} => [r r1| |//]; last by rewrite -mu0 ltxx ltry.
  under eq_integral=> x _ do  rewrite /= poweR_EFin -[(_ `^ _)%R]ger0_norm ?powR_ge0//=.
  rewrite (@integral_abs_eq0 _ _ _ _ setT setT (fun x => (`|f x| `^ r)%:E))//.
    by rewrite poweR0e// invr_neq0//gt_eqF// -lte_fin (lt_le_trans _ r1).
  apply/measurable_EFinP/(@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
  exact: measurableT_comp.
move: p q => [p| |//] [q| |]// p1 q1.
- rewrite le_eqVlt => /predU1P[[->]//|]; rewrite lte_fin => pq f.
  rewrite inE/= => /andP[/[!inE]/= mf] ffin.
  apply/andP; split; rewrite inE//=.
  move: (ffin); rewrite /finite_norm.
  have p0 : (0 < p)%R by rewrite (lt_le_trans ltr01).
  have pN0 : p != 0%R by rewrite gt_eqF.
  have q0 : (0 < q)%R by rewrite (lt_le_trans ltr01).
  have qinv0 : q^-1 != 0%R by rewrite invr_neq0// gt_eqF.
  pose r := q / p.
  pose r' := (1 - r^-1)^-1.
  have := @hoelder _ _ _ mu (fun x => `|f x| `^ p)%R (cst 1)%R r r'.
  rewrite (_ : (_ \* cst 1)%R = (fun x => `|f x| `^ p))%R -?fctM ?mulr1//.
  rewrite Lnorm_cst1 unlock /Lnorm invr1.
  have mfp : measurable_fun [set: T] (fun x : T => (`|f x| `^ p)%R).
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  have m1 : measurable_fun [set: T] (@cst _ R 1%R) by exact: measurable_cst.
  have r0 : (0 < r)%R by rewrite/r divr_gt0.
  have r'0 : (0 < r')%R.
    by rewrite /r' invr_gt0 subr_gt0 invf_lt1 ?(lt_trans ltr01)//;
      rewrite /r ltr_pdivlMr// mul1r.
  have rr'1 : r^-1 + r'^-1 = 1%R.
    by rewrite /r' /r invf_div invrK addrCA subrr addr0.
  move=> /(_ mfp m1 r0 r'0 rr'1).
  under [in leLHS] eq_integral do rewrite /= poweR_EFin powRr1// norm_powR// normrE.
  under [in leRHS] eq_integral do
    rewrite /= poweR_EFin norm_powR// normr_id -powRrM mulrCA divff// mulr1.
  rewrite [X in X <= _]poweRe1; last
    by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
  move=> h1 /lty_poweRy h2.
  apply/poweR_lty => //=; apply /le_lt_trans.
  under eq_integral do rewrite poweR_EFin; apply h1.
  rewrite muleC lte_mul_pinfty ?poweR_ge0 ?fin_num_poweR ?fin_num_measure//.
  rewrite poweR_lty//=. 
  under eq_integral do rewrite -poweR_EFin -abse_EFin; apply h2.
  by rewrite lte_fin invr_gt0.
- have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
  move=> _ f.
  rewrite !inE => /andP[/[1!inE]/= mf].
  rewrite !inE/= /finite_norm unlock /Lnorm mu_pos => supf_lty.
  apply/andP; split; rewrite inE//= /finite_norm unlock /Lnorm.
  rewrite poweR_lty//; move: supf_lty => /ess_supr_bounded[M fM].
  rewrite (@le_lt_trans _ _ (\int[mu]_x (M `^ p)%:E)); [by []| |]; last first.
    by rewrite integral_cst// ltey_eq fin_numM ?fin_num_measure.
  apply: ae_ge0_le_integral => //.
  + by move=> x _; rewrite poweR_EFin lee_fin powR_ge0.
  + under eq_fun do rewrite poweR_EFin; apply/measurable_EFinP.
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  + by move=> x _; rewrite lee_fin powR_ge0.
  + apply: filterS fM => t/= ftM _.
    rewrite poweR_EFin lee_fin ge0_ler_powR//; first exact: ltW.
    by rewrite nnegrE (le_trans _ ftM).
by move=> _.
Qed.

Lemma lfun_inclusion12 :
  {subset lfun mu 2%:E <= lfun mu 1}.
Proof. by move=> ?; apply: lfun_inclusion => //; rewrite lee1n. Qed.

Lemma lfun_bounded (f : T -> R) M p :
  1 <= p -> measurable_fun [set: T] f -> (forall t, `|f t| <= M)%R -> f \in lfun mu p.
Proof.
move=> p1 mX bX.
apply: (@lfun_inclusion p +oo p1 (ltry _) (leey _)).
rewrite inE/=; apply/andP; split; rewrite inE//=.
rewrite /finite_norm unlock.
case: ifPn => P0//.
apply: (@le_lt_trans _ _ M%:E).
  by rewrite ess_sup_ler.
by rewrite ltry.
Qed.

Lemma lfun_norm (f : T -> R) :
  f \in lfun mu 1 -> (normr \o f) \in lfun mu 1.
Proof.
move=> /andP[].
rewrite !inE/= => mf finf; apply/andP; split.
  by rewrite inE/=; exact: measurableT_comp.
rewrite inE/=/finite_norm.
under [X in 'N[_]__[X]]eq_fun => x do rewrite -abse_EFin.
by rewrite Lnorm_abse.
Qed.

End lfun_inclusion.