import Langlands.AlgebraicGeometry.PointTopology.IntegralClosureWeilRestrictionGenericFiber
import Langlands.Global.AdelicFunctoriality.IntegralTopology
import Langlands.Global.CurvePlaceIntegralClosure

/-! # Actual arithmetic generic fibers of integral Weil models -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry Langlands.Global
open scoped NumberField
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTopology
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceIntegralClosure

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section NumberField

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
  (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [LocallyOfFiniteType Y.hom]

local instance numberFieldGenericFiberLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange (𝓞 L) L Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd Y.hom (Spec.algebraMap (𝓞 L) L)))

/-- The original integer Weil model has the actual field Weil scheme as generic fiber. -/
def numberFieldIntegralWeilRestrictionGenericFiberIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom) :
    ringBaseChange (𝓞 K) K (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y) ≅
      affineChartWeilRestriction K L (ringBaseChange (𝓞 L) L Y) :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso
    (𝓞 K) (𝓞 L) K L Y n j hj

/-- The number-field generic-fiber identification preserves the original counit on all tests. -/
theorem numberFieldIntegralWeilRestrictionGenericFiberIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange (𝓞 K) K
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange (𝓞 L) L Y) T
        (p ≫ (numberFieldIntegralWeilRestrictionGenericFiberIso K L Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison (𝓞 K) (𝓞 L) K L
        (integralClosureFractionTensorEquiv (𝓞 K) (𝓞 L) K L)
        (integralClosureFractionTensorEquiv_one_tmul (𝓞 K) (𝓞 L) K L) Y T p :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso_comparison
    (𝓞 K) (𝓞 L) K L Y n j hj T p

end NumberField

section FunctionField

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [FiniteDimensional K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (v : AlgebraicCurve.Place k K)
  (Y : Over (Spec (CommRingCat.of (curvePlaceIntegralClosure L v))))
  [LocallyOfFiniteType Y.hom]

private instance functionFieldIntegralClosureProjective :
    Module.Projective v.toValuationSubring (curvePlaceIntegralClosure L v) := by
  infer_instance

local instance functionFieldGenericFiberLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange (curvePlaceIntegralClosure L v) L Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd Y.hom
      (Spec.algebraMap (curvePlaceIntegralClosure L v) L)))

/-- The Weil model over the original curve-place valuation ring has the actual field generic fiber. -/
def functionFieldIntegralWeilRestrictionGenericFiberIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom) :
    ringBaseChange v.toValuationSubring K
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y) ≅
      affineChartWeilRestriction K L (ringBaseChange (curvePlaceIntegralClosure L v) L Y) :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso
    v.toValuationSubring (curvePlaceIntegralClosure L v) K L Y n j hj

/-- The function-field generic-fiber identification preserves the original counit on all tests. -/
theorem functionFieldIntegralWeilRestrictionGenericFiberIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange v.toValuationSubring K
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange (curvePlaceIntegralClosure L v) L Y) T
        (p ≫ (functionFieldIntegralWeilRestrictionGenericFiberIso k K L v Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison
        v.toValuationSubring (curvePlaceIntegralClosure L v) K L
        (integralClosureFractionTensorEquiv v.toValuationSubring (curvePlaceIntegralClosure L v) K L)
        (integralClosureFractionTensorEquiv_one_tmul
          v.toValuationSubring (curvePlaceIntegralClosure L v) K L) Y T p :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso_comparison
    v.toValuationSubring (curvePlaceIntegralClosure L v) K L Y n j hj T p

end FunctionField

end Langlands.AlgebraicGeometry.PointTopology
