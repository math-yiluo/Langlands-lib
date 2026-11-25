/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientOrdinarySquare
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-! # Canonical derived comparison for diagonal realization pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)

/-- The canonical completed coefficient map, when it is invertible. -/
abbrev diagonalPullbackCoefficientIso [IsIso (diagonalCompletedCoefficientMap l f)] :=
  asIso (diagonalCompletedCoefficientMap l f)

/-- Completed direct image is the specified ringed-module right adjoint. -/
def diagonalPullbackPushBridge [IsIso (diagonalCompletedCoefficientMap l f)] :
    diagonalTracePush l f ≅ Scheme.proEtaleRingModuleDirectImage f
      (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
      (diagonalPullbackCoefficientIso l f) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)))
    (by intros; ext U x; rfl)

variable (eX : CompletedRealization l X) (eS : CompletedRealization l S)

/-- The normalized ordinary direct-image square in ringed-module coordinates. -/
def diagonalPullbackRightComparison [IsIso (diagonalCompletedCoefficientMap l f)] :
    Scheme.proEtaleRingModuleDirectImage f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f) ⋙ eS.F ≅
      eX.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f :=
  Functor.isoWhiskerRight (diagonalPullbackPushBridge l f).symm eS.F ≪≫
    (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)).ordinary

/-- The unique inverse mate of the normalized ordinary direct-image square. -/
def diagonalPullbackOrdinaryComparison [IsIso (diagonalCompletedCoefficientMap l f)] :
    Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f) ⋙ eX.F ≅
      eS.F ⋙ CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f := by
  let adj := Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
    (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)
  let adjb := CondensedRing.upperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  let alpha := ((mateEquiv adj adjb).symm
    (diagonalPullbackRightComparison l f eX eS).hom)
  have : IsIso alpha := isIso_inverseMate_of_equivalences adj adjb
    (diagonalPullbackRightComparison l f eX eS)
  exact (asIso alpha).symm

/-- The ordinary comparison is fixed by its inverse-mate equation. In particular
an arbitrary automorphism or a negative comparison cannot replace it. -/
theorem diagonalPullbackOrdinaryComparison_mate
    [IsIso (diagonalCompletedCoefficientMap l f)] :
    (mateEquiv
      (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
      (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      (diagonalPullbackOrdinaryComparison l f eX eS).inv) =
        (diagonalPullbackRightComparison l f eX eS).hom := by
  exact ((mateEquiv
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)).apply_symm_apply
        (diagonalPullbackRightComparison l f eX eS).hom)

/-- The canonical ordinary comparison preserves every adjunction transpose.
Source: the unit/counit formula for the inverse mate, applied to each module map.
(blueprint: def-sfb-diagonal-realization-pullback-canonical-comparison). -/
theorem diagonalPullbackOrdinaryComparison_transpose
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (M : DiagonalCompleted l S) (N : DiagonalCompleted l X)
    (m : (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).obj M ⟶ N) :
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _
        ((diagonalPullbackOrdinaryComparison l f eX eS).inv.app M ≫ eX.F.map m) =
      eS.F.map ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv
          M N m) ≫ (diagonalPullbackRightComparison l f eX eS).hom.app N := by
  have h := adjunctionMate_transpose
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (mateEquiv
      (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
      (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      (diagonalPullbackOrdinaryComparison l f eX eS).inv) M N m
  rw [Equiv.symm_apply_apply] at h
  change _ = _ ≫ ((mateEquiv
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (diagonalPullbackOrdinaryComparison l f eX eS).inv).app N) at h
  rw [diagonalPullbackOrdinaryComparison_mate] at h
  exact h

variable [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]

/-- Exact derivation of the ordinary inverse mate, with the canonical geometric
upper-star comparison on the right. -/
def diagonalPullbackDerivedComparison [IsIso (diagonalCompletedCoefficientMap l f)] :
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).mapDerivedCategory ⋙
      eX.F.mapDerivedCategory ≅ eS.F.mapDerivedCategory ⋙ derivedUpper
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f := by
  letI : eS.F.asEquivalence.functor.Additive := inferInstanceAs eS.F.Additive
  letI : eX.F.asEquivalence.functor.Additive := inferInstanceAs eX.F.Additive
  exact Functor.mapDerivedCategorySquareIso (diagonalPullbackOrdinaryComparison l f eX eS) ≪≫
    Functor.isoWhiskerLeft eS.F.mapDerivedCategory
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).symm

/-- The canonical pullback comparison. The coefficient normalization transports the
supplied coefficient isomorphism to the canonical map; the comparison is then exactly
the derived ordinary inverse mate, with no further choice of natural isomorphism.
(blueprint: def-sfb-diagonal-realization-pullback-canonical-comparison). -/
def diagonalRealization_pullback_canonical_comparison
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f) :
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory ⋙
      eX.F.mapDerivedCategory ≅ eS.F.mapDerivedCategory ⋙ derivedUpper
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f := by
  have : IsIso (diagonalCompletedCoefficientMap l f) := by
    rw [← hc]
    infer_instance
  have hcoeff : coeff = diagonalPullbackCoefficientIso l f := Iso.ext hc
  exact hcoeff.symm ▸ diagonalPullbackDerivedComparison l f eX eS

/-- At the canonical coefficient isomorphism, coefficient transport is the identity.
Source: proof irrelevance for the coefficient normalization equation.
(blueprint: def-sfb-diagonal-realization-pullback-canonical-comparison). -/
theorem diagonalRealization_pullback_canonical_comparison_normalized
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (hc : (diagonalPullbackCoefficientIso l f).hom = diagonalCompletedCoefficientMap l f) :
    diagonalRealization_pullback_canonical_comparison l f eX eS
      (diagonalPullbackCoefficientIso l f) hc =
        diagonalPullbackDerivedComparison l f eX eS := by
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
