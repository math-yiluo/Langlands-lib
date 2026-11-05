import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.FunctionFieldIntegralWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality
import Langlands.Global.CurvePlaceIntegralModelFieldTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Function-field integral-model field and integer compatibility -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry Langlands.Global
open scoped Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor
  Langlands.Global.CurvePlaceIntegralTopology
  Langlands.Global.CurvePlaceIntegralModelFieldTensor

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

omit [Finite k] [IsScalarTower k K L] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
private theorem modelFieldFactorModuleTopology (q : CurvePlacesAbove k L v) :
    IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (curvePlaceCompletion v) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- Field points of the actual valuation-ring Weil model identify with all original upper field points. -/
def functionFieldIntegralModelFieldPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom) :
    letI : TopologicalSpace (RingPoint v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletion v)) :=
      schemePointTopology v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletion v)
    letI : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
        (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)) :=
      fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)
    RingPoint v.toValuationSubring
        (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletion v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)) := by
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Finite (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun q => CurvePlaceCompletionExtension.localFinite v q
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Free (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Free.of_divisionRing _ _
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Projective.of_free
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    modelFieldFactorModuleTopology k K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlaceIntegralModelFieldTensor.tensorEquiv v)
    (CurvePlaceIntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj

/-- Every upper field component retains the original valuation-ring model counit. -/
theorem functionFieldIntegralModelFieldPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom)
    (p : RingPoint v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletion v))
    (q : CurvePlacesAbove k L v) :
    functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletion v)
          (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
          (CurvePlaceIntegralModelFieldTensor.tensorEquiv v)
          (CurvePlaceIntegralModelFieldTensor.tensorEquiv_one_tmul v) q ≫
        affineChartWeilRestrictionComparison v.toValuationSubring (curvePlaceIntegralClosure L v) Y
          (ringTest v.toValuationSubring (curvePlaceCompletion v)) p := by
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Finite (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun q => CurvePlaceCompletionExtension.localFinite v q
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Free (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Free.of_divisionRing _ _
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Projective.of_free
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    modelFieldFactorModuleTopology k K L v
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlaceIntegralModelFieldTensor.tensorEquiv v)
    (CurvePlaceIntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj p q
  let : TopologicalSpace (RingPoint v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletion v)) :=
    schemePointTopology v.toValuationSubring
      (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletion v)
  let : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
      (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)) :=
    fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)
  have hh : functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletion v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (CurvePlaceIntegralModelFieldTensor.tensorEquiv v)
        (CurvePlaceIntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj := rfl
  rw [hh]
  exact h

/-- Extending integral coefficients commutes with the actual original-model Weil homeomorphisms. -/
theorem functionFieldIntegralModelFieldPointHomeomorph_integralToField
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom)
    (p : RingPoint v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletionIntegers v)) (q : CurvePlacesAbove k L v) :
    functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj
        (p.changeRing (Algebra.algHom v.toValuationSubring (curvePlaceCompletionIntegers v) (curvePlaceCompletion v))) q =
      (functionFieldIntegralWeilRestrictionPointHomeomorph k K L v Y n j hj p q).changeRing
        (Algebra.algHom (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1)) := by
  rw [functionFieldIntegralModelFieldPointHomeomorph_counit,
    functionFieldIntegralWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural
    v.toValuationSubring (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers v) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlaceIntegralTensor.integralTensorEquiv v) (CurvePlaceIntegralTensor.integralTensorEquiv_one_tmul v)
    (CurvePlaceIntegralModelFieldTensor.tensorEquiv v) (CurvePlaceIntegralModelFieldTensor.tensorEquiv_one_tmul v)
    (Algebra.algHom v.toValuationSubring (curvePlaceCompletionIntegers v) (curvePlaceCompletion v))
    (fun q => Algebra.algHom (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1))
    (fun _ _ => rfl) Y p q

/-- A field point of the original Weil model is integral exactly when all its upper components are integral. -/
theorem functionFieldIntegralModelFieldPointHomeomorph_integral_iff
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceIntegralClosure L v) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceIntegralClosure L v) n = Y.hom)
    (p : RingPoint v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y) (curvePlaceCompletion v)) :
    (∃ z : RingPoint v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
        (curvePlaceCompletionIntegers v),
      z.changeRing (Algebra.algHom v.toValuationSubring (curvePlaceCompletionIntegers v) (curvePlaceCompletion v)) = p) ↔
    ∀ q : CurvePlacesAbove k L v,
      ∃ z : RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1),
        z.changeRing (Algebra.algHom (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1)) =
          functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj p q := by
  classical
  let : TopologicalSpace (RingPoint v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletionIntegers v)) :=
    schemePointTopology v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y) (curvePlaceCompletionIntegers v)
  let : ∀ q : CurvePlacesAbove k L v,
      TopologicalSpace (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)) :=
    fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletionIntegers q.1)
  let : TopologicalSpace (RingPoint v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y)
      (curvePlaceCompletion v)) :=
    schemePointTopology v.toValuationSubring (affineChartWeilRestriction v.toValuationSubring (curvePlaceIntegralClosure L v) Y) (curvePlaceCompletion v)
  let : ∀ q : CurvePlacesAbove k L v,
      TopologicalSpace (RingPoint (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)) :=
    fun q => schemePointTopology (curvePlaceIntegralClosure L v) Y (curvePlaceCompletion q.1)
  let eI := functionFieldIntegralWeilRestrictionPointHomeomorph k K L v Y n j hj
  let eF := functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj
  constructor
  · rintro ⟨z, rfl⟩ q
    exact ⟨eI z q, (functionFieldIntegralModelFieldPointHomeomorph_integralToField
      k K L v Y n j hj z q).symm⟩
  · intro h
    choose t ht using h
    refine ⟨eI.symm t, ?_⟩
    apply eF.injective
    apply funext
    intro q
    change functionFieldIntegralModelFieldPointHomeomorph k K L v Y n j hj _ q = _
    rw [functionFieldIntegralModelFieldPointHomeomorph_integralToField]
    have he : eI (eI.symm t) q = t q := congrFun (eI.apply_symm_apply t) q
    exact (congrArg (fun z => z.changeRing
      (Algebra.algHom (curvePlaceIntegralClosure L v) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1))) he).trans (ht q)

end Langlands.AlgebraicGeometry.PointTopology
