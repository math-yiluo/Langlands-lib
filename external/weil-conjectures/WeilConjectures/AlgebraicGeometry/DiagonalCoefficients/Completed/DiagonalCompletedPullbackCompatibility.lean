/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback

import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedClassPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedTracePullback

/-! # Completed diagonal base change before scalar extension

Source: diagonal coefficient changes, paragraph (3).
(blueprint: lem-diagonal-completed-pullback-compatibility).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance] completedRealization_shiftedLine_isIso

private theorem realizedTrace_eq (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (square : CompletedPushSquare l f eX eS t.Rc R)
    (trace : R.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (htrace : CompletedTraceCompatibility l f eX eS t R square trace) :
    inv (R.R.map (eX.shiftedLine l X)) ≫ square.derived.iso.inv.app _ ≫
      eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S = trace := by
  have heq := htrace
  dsimp only [CompletedTraceCompatibility] at heq
  rw [heq]
  simp only [Iso.inv_hom_id_app_assoc, IsIso.inv_hom_id_assoc]

private theorem tracePullback_of_realized (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (square : IsPullback hX f' f hS)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (eX' : CompletedRealization l X') (eS' : CompletedRealization l S')
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (t' : DiagonalTrace.Result l (ULift.{u} (Padic l)) f')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (hcanonical' : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f') D' canonical')
    (push : CompletedPushSquare l f eX eS t.Rc D)
    (push' : CompletedPushSquare l f' eX' eS' t'.Rc D')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS)
    (trace : D.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (trace' : D'.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X') 0).obj
        (zlLine l X'))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S')
    (htrace : CompletedTraceCompatibility l f eX eS t D push trace)
    (htrace' : CompletedTraceCompatibility l f' eX' eS' t' D' push' trace') :
    TracePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) f f' hX hS square.w.symm
      D D' canonical canonical' line c trace trace' := by
  have ht := diagonalCompletedTrace_pullback l f f' hX hS square hunit hunit'
    eX eS eX' eS' t t' D D' canonical canonical' hcanonical hcanonical' push push' line c
  dsimp only at ht
  rw [realizedTrace_eq l _ _ _ _ _ _ _ htrace,
    realizedTrace_eq l _ _ _ _ _ _ _ htrace'] at ht
  exact ht

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
