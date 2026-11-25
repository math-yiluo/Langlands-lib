/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackCoreA
import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralReductionHomology
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteImmersionConstructibilityInterval

/-! # Finite reductions of ordinary immersion pullback

Source: localization Step 6, finite constructibility; Stacks Tags 09AK, 09AL and 09B5.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme.ImmersionCompletedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private theorem coefficientIso_eq (T : Scheme.{u}) :
    (adicLisseForget T).mapIso (completedRingIso l E T) =
      integralDetailedCoefficientComparison T l E := by
  apply (integralDetailedCoefficientComparison_exists T l E).unique
    ?_ (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  intro n
  have hq : quotientEquiv l E n = integralCoefficientULift l E n :=
    (quotientEquiv_exists l E n).unique
      (quotientEquiv_exists l E n).exists.choose_spec
      (integralCoefficientULift_exists l E n).exists.choose_spec
  have h := congrArg ((adicLisseForget T).map)
    ((completedRingIso_exists l E T).exists.choose_spec n)
  have hp : (adicLisseForget T).map
      (completedIntegralCommRingProjectionUnrestricted l E T n) =
      limit.π (integralCoefficientSheafSystem l E T) (op n) := by
    apply Sheaf.hom_ext
    ext U x
    rfl
  simpa only [Functor.map_comp, hp, Functor.mapIso_hom, completedRingIso,
    finiteRingIso, integralDetailedLevelComparison, hq] using h

private theorem back_eq (T : Scheme.{u}) :
    integralDetailedTransport T l E = pbcDerivedRestrict (completedRingIso l E T).hom := by
  have h := congrArg Iso.hom (coefficientIso_eq l E T)
  have := (integralDetailedCoefficientRestriction_exact T l E).1
  have := (integralDetailedCoefficientRestriction_exact T l E).2
  dsimp only [integralDetailedTransport, pbcDerivedRestrict, pbcRestrict]
  simp only [← h]
  rfl

private def roundTripCompleted (T : Scheme.{u}) :
    transport l E T ⋙ integralDetailedTransport T l E ≅ 𝟭 _ := by
  rw [back_eq l E T]
  let e := Classical.choice
    (IntegralCoefficientPresentation.restrict_equivalence (completedRingIso l E T)).2.2.2
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private def roundTripDetailed (T : Scheme.{u}) :
    integralDetailedTransport T l E ⋙ transport l E T ≅ 𝟭 _ := by
  rw [back_eq l E T]
  let e := Classical.choice
    (IntegralCoefficientPresentation.restrict_equivalence (completedRingIso l E T)).2.2.1
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private def ordinaryComparison
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) ≅
      (ordinaryIntegralDerivedPull l E f).obj ((transport l E X).obj K) := by
  let C := Classical.choice (pbc_integral_pullback_identification_exists l E f)
  exact (transport l E Y).mapIso
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).mapIso
        ((roundTripCompleted l E X).app K).symm ≪≫
      (C.derivedIso.app ((transport l E X).obj K)).symm) ≪≫
    (roundTripDetailed l E Y).app _

end AlgebraicGeometry.Scheme.ImmersionCompletedPullback
