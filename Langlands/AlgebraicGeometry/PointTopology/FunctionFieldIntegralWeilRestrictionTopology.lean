import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.Global.CurvePlaceIntegralTopology

/-! # Actual integral Weil point topology at all upper function-field places -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry Langlands.Global
open scoped Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (v : AlgebraicCurve.Place k K)
  (Y : Over (Spec (CommRingCat.of (curvePlaceIntegralClosure L v))))
  [LocallyOfFiniteType Y.hom]

private instance integralClosureProjective :
    Module.Projective v.toValuationSubring (curvePlaceIntegralClosure L v) := by
  infer_instance

/-- Integral points of the actual relative Weil scheme are homeomorphic to
all original upper completed-integer points, for a projectively immersed model. -/
def functionFieldIntegralWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom) :
    letI : TopologicalSpace (RingPoint v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletionIntegers v)) :=
      schemePointTopology v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletionIntegers v)
    letI : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
        (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)) :=
      fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)
    RingPoint v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletionIntegers v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)) := by
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Finite (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.localFinite v
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.localProjective v
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.moduleTopology v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (CurvePlaceIntegralTensor.integralTensorEquiv v)
    (CurvePlaceIntegralTensor.integralTensorEquiv_one_tmul v) Y n j hj

/-- Each integral upper component is the original relative Weil counit along
the corresponding actual completed-integer factor test spectrum. -/
theorem functionFieldIntegralWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom)
    (p : RingPoint v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletionIntegers v))
    (q : CurvePlacesAbove k L v) :
    functionFieldIntegralWeilRestrictionPointHomeomorph k K L v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers v)
          (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
          (CurvePlaceIntegralTensor.integralTensorEquiv v)
          (CurvePlaceIntegralTensor.integralTensorEquiv_one_tmul v) q ≫
        affineChartWeilRestrictionComparison v.toValuationSubring (curvePlaceIntegralClosure L v) Y
          (ringTest v.toValuationSubring (curvePlaceCompletionIntegers v)) p := by
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Finite (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.localFinite v
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.localProjective v
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletionIntegers v) (curvePlaceCompletionIntegers q.1) :=
    CurvePlaceIntegralTopology.moduleTopology v
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (CurvePlaceIntegralTensor.integralTensorEquiv v)
    (CurvePlaceIntegralTensor.integralTensorEquiv_one_tmul v) Y n j hj p q
  let : TopologicalSpace (RingPoint v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletionIntegers v)) :=
    schemePointTopology v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletionIntegers v)
  let : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
      (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)) :=
    fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)
  have hh : functionFieldIntegralWeilRestrictionPointHomeomorph k K L v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
        (CurvePlaceIntegralTensor.integralTensorEquiv v)
        (CurvePlaceIntegralTensor.integralTensorEquiv_one_tmul v) Y n j hj := rfl
  rw [hh]
  exact h

end Langlands.AlgebraicGeometry.PointTopology
