/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientPushAction

/-! # Ordinary direct image under normalized completed realizations

Source: diagonal tower coefficient changes, initial coefficient identification.
(blueprint: lem-diagonal-completed-ordinary-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem section_action_lowerStar {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (N : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
    (U : S.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S).obj.obj U)
    (x : N.X.obj.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
    coefficientSectionAction
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj N)
        U a x =
      coefficientSectionAction N ((Scheme.proEtaleBaseChange f).op.obj U)
        (condensedPushScalarSection f U a)
        x := by
  exact CategoryTheory.SheafModuleSection.action_pushforward
    (Scheme.proEtaleBaseChange f)
    (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) N U a x

private def ordinaryUnderlyingIso {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) :
    (eS.F.obj ((diagonalTracePush l f).obj M)).X ≅
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj
        (eX.F.obj M)).X :=
  completedPushInputIso f eS M ≪≫
    (lowerStar Ab.{u + 1} f).mapIso (eX.underlying.app M).symm

private theorem ordinaryUnderlyingIso_hom_apply {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    (ordinaryUnderlyingIso f eX eS M).hom.hom.app U x =
      completedRealizationSectionInv eX M ((Scheme.proEtaleBaseChange f).op.obj U)
        (completedPushInputSection f eS M U x) := by
  rfl

private theorem ordinaryUnderlyingIso_natural {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    {M N : DiagonalCompleted l X} (g : M ⟶ N) :
    (eS.F.map ((diagonalTracePush l f).map g)).hom ≫
        (ordinaryUnderlyingIso f eX eS N).hom =
      (ordinaryUnderlyingIso f eX eS M).hom ≫
        (lowerStar Ab.{u + 1} f).map (eX.F.map g).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  let V := (Scheme.proEtaleBaseChange f).op.obj U
  have hs := congrArg (fun q ↦ q.hom.app U)
    (eS.underlying.hom.naturality ((diagonalTracePush l f).map g))
  have hx := congrArg (fun q ↦ q.hom.app V) (eX.underlying.inv.naturality g)
  have hs' := congrArg (fun q ↦ q ≫ (eX.underlying.inv.app N).hom.app V) hs
  have hx' := congrArg (fun q ↦ (eS.underlying.hom.app
    ((diagonalTracePush l f).obj M)).hom.app U ≫ q) hx
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Category.assoc] at hs' hx'
  exact hs'.trans hx'

private theorem ordinaryUnderlyingIso_action_left {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (c : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    (ordinaryUnderlyingIso f eX eS M).hom.hom.app U
        (coefficientSectionAction (eS.F.obj ((diagonalTracePush l f).obj M)) U
          (completedRealizationScalarSection eS U c) x) =
      completedRealizationSectionInv eX M ((Scheme.proEtaleBaseChange f).op.obj U)
        (completedPushScalar f U c • completedPushInputSection f eS M U x) := by
  rw [ordinaryUnderlyingIso_hom_apply]
  exact congrArg (completedRealizationSectionInv eX M
    ((Scheme.proEtaleBaseChange f).op.obj U))
      (completedPushInputIso_section_action f eS M U c x)

private theorem ordinaryUnderlyingIso_action_right {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (c : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    coefficientSectionAction ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj (eX.F.obj M)) U
        (completedRealizationScalarSection eS U c)
        ((ordinaryUnderlyingIso f eX eS M).hom.hom.app U x) =
      completedRealizationSectionInv eX M ((Scheme.proEtaleBaseChange f).op.obj U)
        (completedPushScalar f U c • completedPushInputSection f eS M U x) := by
  rw [ordinaryUnderlyingIso_hom_apply, section_action_lowerStar,
    completedRealization_scalar_push]
  exact completedRealization_section_action_typed l X eX M _ _ _

private theorem ordinaryUnderlyingIso_sections {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S).obj.obj U)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    (ordinaryUnderlyingIso f eX eS M).hom.hom.app U
        (coefficientSectionAction (eS.F.obj ((diagonalTracePush l f).obj M)) U a x) =
      coefficientSectionAction ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj (eX.F.obj M)) U a
        ((ordinaryUnderlyingIso f eX eS M).hom.hom.app U x) := by
  let c := completedRealizationScalarInv eS U a
  have h := (ordinaryUnderlyingIso_action_left f eX eS M U c x).trans
    (ordinaryUnderlyingIso_action_right f eX eS M U c x).symm
  simpa only [c, completedRealizationScalarInv_hom] using h

private theorem ordinaryUnderlyingIso_linear {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) :
    Mod.act (eS.F.obj ((diagonalTracePush l f).obj M)).X ≫
        (ordinaryUnderlyingIso f eX eS M).hom =
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) ◁
          (ordinaryUnderlyingIso f eX eS M).hom ≫
        Mod.act ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj (eX.F.obj M)).X := by
  refine CategoryTheory.SheafModuleSection.linear_of_action
    (M := eS.F.obj ((diagonalTracePush l f).obj M))
    (N := (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj
      (eX.F.obj M)) (ordinaryUnderlyingIso f eX eS M).hom ?_
  exact ordinaryUnderlyingIso_sections f eX eS M

private theorem conjugate_cancel {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A : D} {B E : C} (a : A ≅ H.obj B) (b : E ≅ B) :
    (a ≪≫ H.mapIso b.symm).hom ≫ H.map b.hom = a.hom := by
  simp

private theorem ordinaryUnderlyingIso_normalization {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) :
    HEq ((ordinaryUnderlyingIso f eX eS M).hom ≫
      (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
      (eS.underlying.hom.app ((diagonalTracePush l f).obj M)) := by
  exact (heq_of_eq (conjugate_cancel (lowerStar Ab.{u + 1} f)
    (completedPushInputIso f eS M) (eX.underlying.app M))).trans
      (completedPushInputIso_hom_heq f eS M)

/-- A normalized completed realization commutes with ordinary direct image.
This contains no derived functor or supported-source assertion.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), coefficient/direct-image
identification; integral pullback compatibility of lemma-comparison-completed-coefficients.
(blueprint: lem-diagonal-completed-ordinary-square).

Proof: identify both underlying abelian sheaves with direct image of the original
underlying sheaf. Transport the identity through the two underlying-sheaf
isomorphisms. The unit normalizations determine the ring comparison at every
finite projection. Naturality on maps from free modules on local representables
then identifies each realization's module action with scalar transport along
that ring comparison. Pullback compatibility of the integral comparison makes
the transported identity linear. Its inverse is linear by the same argument,
so it is an isomorphism. Naturality follows from
naturality of the underlying comparisons and faithfulness of forgetting the
module action. The resulting underlying-sheaf equation is exactly the required
normalization. -/
theorem completedCoefficientOrdinarySquare_exists (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    Nonempty (CompletedOrdinarySquare l f eX eS) := by
  let e : diagonalTracePush l f ⋙ eS.F ≅
      eX.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f :=
    NatIso.ofComponents
      (fun M ↦ Mod.isoMk (ordinaryUnderlyingIso f eX eS M)
        (ordinaryUnderlyingIso_linear f eX eS M)) (by
      intro M N g
      apply Mod.hom_ext
      exact ordinaryUnderlyingIso_natural f eX eS g)
  refine ⟨⟨e, ?_⟩⟩
  intro M
  exact ordinaryUnderlyingIso_normalization f eX eS M

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
