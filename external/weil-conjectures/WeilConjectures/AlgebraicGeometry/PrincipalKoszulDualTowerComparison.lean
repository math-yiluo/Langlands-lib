/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualEndpoints
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # The strict singleton Koszul dual and principal cone towers

Source: Stacks Project, algebraization.tex, proof of Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
attribute [local irreducible] homComplexFunctor homComplexπ
open MonoidalCategory

section Assembly
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (a : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)

attribute [local instance 20000] ringedCompletionHasSheafCompose
attribute [local irreducible] ringedHomUnitEvaluationIso

open PrincipalKoszulDualTerms

private def finiteDualLevel (m : ℕ) :
    principalKoszul R a m ≅
      (ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m) :=
  HomologicalComplex.Hom.isoOfComponents (finiteDualTerm R a m) (by
    intro q t h
    by_cases hq : q = -1
    · subst q
      have ht : t = 0 := by change -1 + 1 = t at h; omega
      subst t
      exact finiteDualTerm_nonzero_differential R a m
    · by_cases h0 : q = 0
      · subst q
        have ht : t = 1 := by exact h.symm
        subst t
        exact (dualOtherTerm R a m 1 (by decide) (by decide)).eq_of_tgt _ _
      · exact (coneOtherTerm R a m q h0 hq).eq_of_src _ _)

private def finiteDualTower :
    principalKoszulTower R a ≅
      ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩) := by
  let f : principalKoszulTower R a ⟶
      ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩) :=
    NatTrans.ofOpSequence (fun m ↦ (finiteDualLevel R a m).hom) (fun m ↦ by
      apply HomologicalComplex.hom_ext
      intro q
      change ((principalKoszulTower R a).map
          (homOfLE (Nat.le_succ m)).op).f q ≫ (finiteDualTerm R a m q).hom =
        (finiteDualTerm R a (m + 1) q).hom ≫ _
      erw [show (principalKoszulTower R a).map (homOfLE (Nat.le_succ m)).op =
        principalKoszulTransition R a m from
          Functor.ofOpSequence_map_homOfLE_succ _ m]
      by_cases hq : q = 0 ∨ q = -1
      · exact (finiteDualTerm_transition_unit R a).1 m q hq
      · exact (coneOtherTerm R a (m + 1) q
          (fun h ↦ hq (Or.inl h)) (fun h ↦ hq (Or.inr h))).eq_of_src _ _)
  letI (m : ℕᵒᵖ) : IsIso (f.app m) := by
    change IsIso (finiteDualLevel R a m.unop).hom
    infer_instance
  letI : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

private theorem finiteDualTower_unit (m : ℕ) :
    CochainComplex.mappingCone.inr (scalarComplex R a m) ≫
        (finiteDualTower R a).hom.app (op m) =
      ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m := by
  apply HomologicalComplex.hom_ext
  intro q
  change _ ≫ (finiteDualTerm R a m q).hom = _
  by_cases hq : q = 0
  · subst q
    exact (finiteDualTerm_transition_unit R a).2 m
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq).eq_of_src _ _

private def tensorExchange (P : ringedSiteComplex R) :
    koszulTensorFunctor R P ≅ (ringedKoszulTensor R).obj P := by
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  letI := Classical.choice (SheafOfModules.tensorClosed R).1
  letI := Classical.choice (SheafOfModules.tensorClosed R).2.1
  refine NatIso.ofComponents (fun Q ↦ CochainComplex.Monoidal.braiding Q P) ?_
  intro Q Q' f
  exact CochainComplex.Monoidal.braiding_naturality_left (L := P) f

private def tensorDualTower (P : ringedSiteComplex R) :
    koszulTensorTower R P a ≅
      (ringedKoszulTensorTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj P := by
  change principalKoszulTower R a ⋙ koszulTensorFunctor R P ≅
    ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩) ⋙
      (ringedKoszulTensor R).obj P
  exact Functor.isoWhiskerRight (finiteDualTower R a) (koszulTensorFunctor R P) ≪≫
    Functor.isoWhiskerLeft (ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩))
      (tensorExchange R P)

private theorem tensorExchange_unit (P : ringedSiteComplex R) :
    koszulTensorUnitInclusion R P ≫
        (tensorExchange R P).hom.app (ringedSiteRingComplex R) =
      (ringedKoszulRightUnitIso R P).inv := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let : MonoidalCategory (ringedSiteComplex R) :=
    HomologicalComplex.monoidalCategory _ (.up ℤ)
  let : BraidedCategory (ringedSiteComplex R) :=
    CochainComplex.Monoidal.braidedCategory
  change koszulTensorUnitInclusion R P ≫
    (CochainComplex.Monoidal.braiding (ringedSiteRingComplex R) P).hom = _
  have hl : koszulTensorUnitInclusion R P = (HomologicalComplex.leftUnitor P).inv := by
    apply HomologicalComplex.hom_ext
    intro q
    exact (HomologicalComplex.leftUnitor'_inv P q).symm
  exact (congrArg (fun f ↦ f ≫
    (CochainComplex.Monoidal.braiding (ringedSiteRingComplex R) P).hom) hl).trans
      (leftUnitor_inv_braiding P)

private theorem tensorUnitTransport
    {A B : Type*} [Category A] [Category B] (T S : A ⥤ B) (E : T ≅ S)
    {U K Q : A} {P : B} (i : U ⟶ K) (f : K ⟶ Q) (d : U ⟶ Q)
    (j : P ⟶ T.obj U) (r : P ⟶ S.obj U) (h : i ≫ f = d)
    (hu : j ≫ E.hom.app U = r) :
    (j ≫ T.map i) ≫ (T.map f ≫ E.hom.app Q) = r ≫ S.map d := by
  rw [Category.assoc, ← Category.assoc (T.map i), ← T.map_comp, h,
    E.hom.naturality, ← Category.assoc, hu]

private theorem tensorDualTower_unit (P : ringedSiteComplex R) (m : ℕ) :
    (koszulStrictAugmentation R P a).app (op m) ≫
        (tensorDualTower R a P).hom.app (op m) =
      ringedKoszulTensorUnitComponent R 1 (fun _ ↦ ⟨a.val, a.property⟩) P (op m) := by
  change (koszulTensorUnitInclusion R P ≫
      (koszulTensorFunctor R P).map
        (CochainComplex.mappingCone.inr (scalarComplex R a m))) ≫
      ((koszulTensorFunctor R P).map ((finiteDualTower R a).hom.app (op m)) ≫
        (tensorExchange R P).hom.app _) =
    (ringedKoszulRightUnitIso R P).inv ≫ ((ringedKoszulTensor R).obj P).map
      (ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m)
  exact tensorUnitTransport _ _ (tensorExchange R P) _ _ _ _ _
    (finiteDualTower_unit R a m) (tensorExchange_unit R P)

end Assembly

/-- The singleton dual Koszul tensor tower is the principal negative cone tensor tower,
including its degree-zero augmentation, before applying inverse limit or localization.

Source: Stacks Project, algebraization.tex, proof of Tag 0A0E, the identification
of the dual positive Koszul complex with the negative Koszul complex.
(auxiliary; not a blueprint node).

Proof: remove the right tensor unit in the singleton positive Koszul diagram.
In degree q the internal Hom into R[0] has only the component with source degree -q;
all other product factors are zero. Project to that component and evaluate at one.
This identifies its two nonzero terms with R in degrees -1 and 0. In degree -1
its Hom differential is -(-1)^(-1) times precomposition, hence multiplication by
a^(n+1), exactly the principal cone differential. Off these degrees both complexes
are zero. The inverse maps insert the unique surviving Hom component. Dualizing
the positive transition (1,a) gives (a,1), the principal cone transition. The dual
of the projection to degree zero gives the cone inclusion. Tensor these maps with P,
using symmetry to exchange P and the finite factor. The total tensor signs give
a chain isomorphism: on the summand in bidegree (i,j) the interchange map
is (-1)^(i*j) times the module symmetry. The augmentation has finite-factor
degree zero and thus acquires no sign. The
transition equations give an isomorphism of strict towers; transpose it degreewise.
The component equation is precisely the degree-zero inclusion calculation. All
formulas work for zero and invertible sections, P=0, the zero ring and empty sites;
no regularity or K-flatness of P is used. -/
theorem principalKoszul_dual_tower_comparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ e : koszulTowerComplex R (koszulTensorTower R P a) ≅
        ringedKoszulTensorTowerComplex R 1 (fun _ ↦ ⟨a.val, a.property⟩) P,
      ∀ (m : ℕ) (q : ℤ),
        ((koszulStrictAugmentation R P a).app (op m)).f q ≫
            (e.hom.f q).app (op m) =
          (ringedKoszulTensorUnitComponent R 1
            (fun _ ↦ ⟨a.val, a.property⟩) P (op m)).f q := by
  let E := tensorDualTower R a P
  let e : koszulTowerComplex R (koszulTensorTower R P a) ≅
      ringedKoszulTensorTowerComplex R 1 (fun _ ↦ ⟨a.val, a.property⟩) P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ NatIso.ofComponents
        (fun m ↦ (HomologicalComplex.eval _ (.up ℤ) q).mapIso (E.app m))
        (fun {m n} f ↦ congrArg (fun g ↦ g.f q) (E.hom.naturality f)))
      (by
        intro q t h
        apply NatTrans.ext
        funext m
        have ht : q + 1 = t := h
        subst t
        change (E.hom.app m).f q ≫ _ = _ ≫ (E.hom.app m).f (q + 1)
        simpa only [ringedKoszulTensorTowerComplex, CochainComplex.of_d, koszulTowerComplex,
            Functor.whiskerLeft, HomologicalComplex.dNatTrans] using
          (E.hom.app m).comm q (q + 1))
  refine ⟨e, fun m q ↦ ?_⟩
  exact congrArg (fun g ↦ g.f q) (tensorDualTower_unit R a P m)

end CategoryTheory
