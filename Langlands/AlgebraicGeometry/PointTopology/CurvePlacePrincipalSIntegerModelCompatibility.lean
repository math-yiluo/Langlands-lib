import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.CurvePlacePrincipalSIntegerWeilIntegralTopology
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality
import Langlands.Global.SIntegerCompletedFieldTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Actual principal curve S-integer model field and integer compatibility -/

noncomputable section

universe u

open CategoryTheory Topology IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry Langlands.Global
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlacePrincipalSIntegerFieldTensor
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
  (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))
  [LocallyOfFiniteType Y.hom]

omit [Finite k] [IsScalarTower k K L] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
private theorem modelFieldFactorModuleTopology (q : CurvePlacesAbove k L v) :
    IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (curvePlaceCompletion v) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- Field points of the actual valuation-ring Weil model identify with all original upper field points. -/
def curvePlacePrincipalSIntegerModelFieldPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom) :
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletion v)) :=
      schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletion v)
    letI : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
        (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)) :=
      fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletion v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)) := by
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
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) Y n j hj

/-- Every upper field component retains the original valuation-ring model counit. -/
theorem curvePlacePrincipalSIntegerModelFieldPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletion v))
    (q : CurvePlacesAbove k L v) :
    curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion v)
          (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
          (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
          (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) q ≫
        affineChartWeilRestrictionComparison (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (ringTest (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletion v)) p := by
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
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) Y n j hj p q
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletion v)) :=
    schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletion v)
  let : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)) :=
    fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)
  have hh : curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) Y n j hj := rfl
  rw [hh]
  exact h

variable [Fact (v ∉ curvePlacePrincipalExceptional k K s (t : K))]

/-- Extending integral coefficients commutes with the actual original-model Weil homeomorphisms. -/
theorem curvePlacePrincipalSIntegerModelFieldPointHomeomorph_integralToField
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletionIntegers v)) (q : CurvePlacesAbove k L v) :
    curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj
        (p.changeRing (Algebra.algHom (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletionIntegers v) (curvePlaceCompletion v))) q =
      (curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph k K L s t v Y n j hj p q).changeRing
        (Algebra.algHom (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1)) := by
  rw [curvePlacePrincipalSIntegerModelFieldPointHomeomorph_counit,
    curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers v) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L) (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v) (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v)
    (Algebra.algHom (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletionIntegers v) (curvePlaceCompletion v))
    (fun q => Algebra.algHom (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1))
    (fun _ _ => rfl) Y p q

/-- A field point of the original Weil model is integral exactly when all its upper components are integral. -/
theorem curvePlacePrincipalSIntegerModelFieldPointHomeomorph_integral_iff
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceCompletion v)) :
    (∃ z : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
        (curvePlaceCompletionIntegers v),
      z.changeRing (Algebra.algHom (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletionIntegers v) (curvePlaceCompletion v)) = p) ↔
    ∀ q : CurvePlacesAbove k L v,
      ∃ z : RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1),
        z.changeRing (Algebra.algHom (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1)) =
          curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj p q := by
  classical
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletionIntegers v)) :=
    schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceCompletionIntegers v)
  let : ∀ q : CurvePlacesAbove k L v,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)) :=
    fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletionIntegers q.1)
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceCompletion v)) :=
    schemePointTopology (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceCompletion v)
  let : ∀ q : CurvePlacesAbove k L v,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)) :=
    fun q => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1)
  let eI := curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph k K L s t v Y n j hj
  let eF := curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj
  constructor
  · rintro ⟨z, rfl⟩ q
    exact ⟨eI z q, (curvePlacePrincipalSIntegerModelFieldPointHomeomorph_integralToField
      k K L s t v Y n j hj z q).symm⟩
  · intro h
    choose zI hzI using h
    refine ⟨eI.symm zI, ?_⟩
    apply eF.injective
    apply funext
    intro q
    change curvePlacePrincipalSIntegerModelFieldPointHomeomorph k K L s t v Y n j hj _ q = _
    rw [curvePlacePrincipalSIntegerModelFieldPointHomeomorph_integralToField]
    have he : eI (eI.symm zI) q = zI q := congrFun (eI.apply_symm_apply zI) q
    exact (congrArg (fun z => z.changeRing
      (Algebra.algHom (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1))) he).trans (hzI q)

end Langlands.AlgebraicGeometry.PointTopology
