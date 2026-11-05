import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.NumberFieldIntegralWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality
import Langlands.Global.AdelicFunctoriality.IntegralModelFieldTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Integral-model Weil points: original integer and field compatibility -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open NumberField IsDedekindDomain
open Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension IntegralTensor IntegralTopology IntegralModelFieldTensor

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))
  (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [LocallyOfFiniteType Y.hom]

private theorem modelFieldFactorModuleTopology (q : FinitePlacesAbove L v) :
    IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) := by
  let : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- Field points of the actual integral-model Weil scheme identify with all original upper field points. -/
def numberFieldIntegralModelFieldPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom) :
    letI : TopologicalSpace (RingPoint (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletion K)) :=
      schemePointTopology (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletion K)
    letI : ∀ q : FinitePlacesAbove L v, TopologicalSpace
        (RingPoint (𝓞 L) Y (q.1.adicCompletion L)) :=
      fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletion L)
    RingPoint (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletion K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoint (𝓞 L) Y (q.1.adicCompletion L)) := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun q => FiniteExtension.local_finite v q.1
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun _ => inferInstance
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    modelFieldFactorModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    (𝓞 K) (𝓞 L) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (IntegralModelFieldTensor.tensorEquiv v)
    (IntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj

/-- Every upper field component retains the original integral-model Weil counit. -/
theorem numberFieldIntegralModelFieldPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom)
    (p : RingPoint (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletion K))
    (q : FinitePlacesAbove L v) :
    numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          (𝓞 K) (𝓞 L) (v.adicCompletion K)
          (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
          (IntegralModelFieldTensor.tensorEquiv v)
          (IntegralModelFieldTensor.tensorEquiv_one_tmul v) q ≫
        affineChartWeilRestrictionComparison (𝓞 K) (𝓞 L) Y
          (ringTest (𝓞 K) (v.adicCompletion K)) p := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun q => FiniteExtension.local_finite v q.1
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun _ => inferInstance
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    modelFieldFactorModuleTopology K L v
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    (𝓞 K) (𝓞 L) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (IntegralModelFieldTensor.tensorEquiv v)
    (IntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj p q
  let : TopologicalSpace (RingPoint (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletion K)) :=
    schemePointTopology (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletion K)
  let : ∀ q : FinitePlacesAbove L v, TopologicalSpace
      (RingPoint (𝓞 L) Y (q.1.adicCompletion L)) :=
    fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletion L)
  have hh : numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        (𝓞 K) (𝓞 L) (v.adicCompletion K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (IntegralModelFieldTensor.tensorEquiv v)
        (IntegralModelFieldTensor.tensorEquiv_one_tmul v) Y n j hj := rfl
  rw [hh]
  exact h

/-- Extending integral coefficients commutes with the actual original-model Weil homeomorphisms. -/
theorem numberFieldIntegralModelFieldPointHomeomorph_integralToField
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom)
    (p : RingPoint (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletionIntegers K)) (q : FinitePlacesAbove L v) :
    numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj
        (p.changeRing (Algebra.algHom (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K))) q =
      (numberFieldIntegralWeilRestrictionPointHomeomorph K L v Y n j hj p q).changeRing
        (Algebra.algHom (𝓞 L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L)) := by
  rw [numberFieldIntegralModelFieldPointHomeomorph_counit,
    numberFieldIntegralWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural
    (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (IntegralTensor.tensorEquiv v) (IntegralTensor.tensorEquiv_one_tmul v)
    (IntegralModelFieldTensor.tensorEquiv v) (IntegralModelFieldTensor.tensorEquiv_one_tmul v)
    (Algebra.algHom (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K))
    (fun q => Algebra.algHom (𝓞 L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L))
    (fun _ _ => rfl) Y p q

/-- A field point of the original Weil model is integral exactly when all its upper components are integral. -/
theorem numberFieldIntegralModelFieldPointHomeomorph_integral_iff
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom)
    (p : RingPoint (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y) (v.adicCompletion K)) :
    (∃ z : RingPoint (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletionIntegers K),
      z.changeRing (Algebra.algHom (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K)) = p) ↔
    ∀ q : FinitePlacesAbove L v,
      ∃ z : RingPoint (𝓞 L) Y (q.1.adicCompletionIntegers L),
        z.changeRing (Algebra.algHom (𝓞 L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L)) =
          numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj p q := by
  classical
  let : TopologicalSpace (RingPoint (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletionIntegers K)) :=
    schemePointTopology (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y) (v.adicCompletionIntegers K)
  let : ∀ q : FinitePlacesAbove L v,
      TopologicalSpace (RingPoint (𝓞 L) Y (q.1.adicCompletionIntegers L)) :=
    fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletionIntegers L)
  let : TopologicalSpace (RingPoint (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletion K)) :=
    schemePointTopology (𝓞 K) (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y) (v.adicCompletion K)
  let : ∀ q : FinitePlacesAbove L v,
      TopologicalSpace (RingPoint (𝓞 L) Y (q.1.adicCompletion L)) :=
    fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletion L)
  let eI := numberFieldIntegralWeilRestrictionPointHomeomorph K L v Y n j hj
  let eF := numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj
  constructor
  · rintro ⟨z, rfl⟩ q
    exact ⟨eI z q, (numberFieldIntegralModelFieldPointHomeomorph_integralToField
      K L v Y n j hj z q).symm⟩
  · intro h
    choose t ht using h
    refine ⟨eI.symm t, ?_⟩
    apply eF.injective
    apply funext
    intro q
    change numberFieldIntegralModelFieldPointHomeomorph K L v Y n j hj _ q = _
    rw [numberFieldIntegralModelFieldPointHomeomorph_integralToField]
    have he : eI (eI.symm t) q = t q := congrFun (eI.apply_symm_apply t) q
    exact (congrArg (fun z => z.changeRing
      (Algebra.algHom (𝓞 L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L))) he).trans (ht q)

end Langlands.AlgebraicGeometry.PointTopology
