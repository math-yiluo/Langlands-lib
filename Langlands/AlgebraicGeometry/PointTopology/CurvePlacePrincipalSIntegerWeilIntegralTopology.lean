import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.Global.CurvePlaceIntegralTopology
import Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor

/-! # Integral Weil point topology for actual global curve S-integer models -/

noncomputable section

universe u

open CategoryTheory Topology AlgebraicCurve IntermediateField
open _root_.AlgebraicGeometry Langlands.Global
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (s : K) [FiniteDimensional k⟮s⟯ K] (t : CurveModel.chartRing k ({s} : Set K))
  [Fact (t ≠ 0)] (v : AlgebraicCurve.Place k K)
  [Fact (v ∉ curvePlacePrincipalExceptional k K s (t : K))]
  (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))
  [LocallyOfFiniteType Y.hom]

/-- Integral points of the actual relative Weil scheme are homeomorphic to
all original upper completed-integer points, for a projectively immersed model. -/
def curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom) :
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletionIntegers v)) :=
      schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletionIntegers v)
    letI : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
        (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)) :=
      fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletionIntegers v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)) := by
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
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L) Y n j hj

/-- Each integral upper component is the original relative Weil counit along
the corresponding actual completed-integer factor test spectrum. -/
theorem curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletionIntegers v))
    (q : CurvePlacesAbove k L v) :
    curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph k K L s t v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers v)
          (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
          (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
          (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L) q ≫
        affineChartWeilRestrictionComparison (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (ringTest (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletionIntegers v)) p := by
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
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L) Y n j hj p q
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletionIntegers v)) :=
    schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletionIntegers v)
  let : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)) :=
    fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)
  have hh : curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph k K L s t v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
        (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
        (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L) Y n j hj := rfl
  rw [hh]
  exact h

end Langlands.AlgebraicGeometry.PointTopology
