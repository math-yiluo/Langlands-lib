/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientScalarPush

/-! # Section actions through the underlying completed pushforward

Source: the ordinary coefficient square, its local action calculation.
(blueprint: lem-sfb-diagonal-completed-push-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem completed_push_smul {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalCompleted l X)
    (U : S.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U)
    (m : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
    @SMul.smul _ (((diagonalTracePush l f).obj M).val.obj U) inferInstance a m =
      completedPushScalar f U a • m := by
  change _ = (_ * 1) • _
  rw [mul_one]
  rfl

/-- Regard the given underlying comparison on a pushed module as a comparison to
ordinary abelian direct image. Source: the completed ringed direct-image construction
(blueprint: lem-sfb-diagonal-completed-push-action). -/
def completedPushInputIso {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) :
    (eS.F.obj ((diagonalTracePush l f).obj M)).X ≅
      (lowerStar Ab.{u + 1} f).obj
        ((diagonalCompletedRestriction l X ⋙ diagonalForget l X).obj M) :=
  eS.underlying.app ((diagonalTracePush l f).obj M)

/-- The comparison has exactly the prescribed underlying map.
Source: the completed ringed direct-image construction
(blueprint: lem-sfb-diagonal-completed-push-action).
Proof: both maps are the same underlying comparison, with definitionally equal targets. -/
theorem completedPushInputIso_hom_heq {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) :
    HEq (completedPushInputIso f eS M).hom
      (eS.underlying.hom.app ((diagonalTracePush l f).obj M)) := by
  rfl

/-- The underlying push comparison evaluated with its original module section type.
Source: the completed direct-image construction
(blueprint: lem-sfb-diagonal-completed-push-action). -/
def completedPushInputSection {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) :=
  (completedPushInputIso f eS M).hom.hom.app U x

/-- The underlying comparison on a pushed module carries its internal action to the
completed scalar action on the original module's sections.

Source: lem-diagonal-completed-ordinary-square, first action calculation.
(blueprint: lem-sfb-diagonal-completed-push-action).

Proof: apply the single-site section-action identity to the pushed module and the section
obtained by the underlying comparison. Cancel the inverse underlying comparison. The
completed pushforward action is restriction of scalars, hence multiplication by the
coefficient map applied to the coefficient; applying it to one gives completedPushScalar. -/
theorem completedPushInputIso_section_action {l : ℕ} [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (eS : CompletedRealization l S)
    (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (c : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U)
    (x : (eS.F.obj ((diagonalTracePush l f).obj M)).X.obj.obj U) :
    completedPushInputSection f eS M U
        (coefficientSectionAction (eS.F.obj ((diagonalTracePush l f).obj M)) U
          (completedRealizationScalarSection eS U c) x) =
      completedPushScalar f U c • completedPushInputSection f eS M U x := by
  let P := (diagonalTracePush l f).obj M
  let m : P.val.obj U := (eS.underlying.hom.app P).hom.app U x
  have hx : (eS.underlying.inv.app P).hom.app U m = x :=
    congrArg (fun q ↦ q.hom.app U x) (eS.underlying.app P).hom_inv_id
  have h := completedRealization_section_action l S eS P U c m
  rw [hx] at h
  have h' := congrArg (fun z ↦ (eS.underlying.hom.app P).hom.app U z) h
  have hc : (eS.underlying.hom.app P).hom.app U
      ((eS.underlying.inv.app P).hom.app U (c • m)) = c • m :=
    congrArg (fun q ↦ q.hom.app U (c • m)) (eS.underlying.app P).inv_hom_id
  exact (h'.trans hc).trans (completed_push_smul f M U c m)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
