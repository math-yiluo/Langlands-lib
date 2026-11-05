import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.Global.AdelicFunctoriality.IntegralTopology

/-! # Actual integral Weil point topology at all upper number-field places -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open NumberField IsDedekindDomain
open Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension IntegralTensor IntegralTopology

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))
  (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [LocallyOfFiniteType Y.hom]

/-- Integral points of the actual relative Weil scheme are homeomorphic to
all original upper completed-integer points, for a projectively immersed model. -/
def numberFieldIntegralWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom) :
    letI : TopologicalSpace (RingPoint (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletionIntegers K)) :=
      schemePointTopology (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletionIntegers K)
    letI : ∀ q : FinitePlacesAbove L v, TopologicalSpace
        (RingPoint (𝓞 L) Y (q.1.adicCompletionIntegers L)) :=
      fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletionIntegers L)
    RingPoint (𝓞 K)
        (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
        (v.adicCompletionIntegers K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoint (𝓞 L) Y (q.1.adicCompletionIntegers L)) := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.localFinite v
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.localProjective v
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.moduleTopology v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (IntegralTensor.tensorEquiv v)
    (IntegralTensor.tensorEquiv_one_tmul v) Y n j hj

/-- Each integral upper component is the original relative Weil counit along
the corresponding actual completed-integer factor test spectrum. -/
theorem numberFieldIntegralWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (𝓞 L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (𝓞 L) n = Y.hom)
    (p : RingPoint (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletionIntegers K))
    (q : FinitePlacesAbove L v) :
    numberFieldIntegralWeilRestrictionPointHomeomorph K L v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K)
          (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
          (IntegralTensor.tensorEquiv v)
          (IntegralTensor.tensorEquiv_one_tmul v) q ≫
        affineChartWeilRestrictionComparison (𝓞 K) (𝓞 L) Y
          (ringTest (𝓞 K) (v.adicCompletionIntegers K)) p := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.localFinite v
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.localProjective v
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) :=
    IntegralTopology.moduleTopology v
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (IntegralTensor.tensorEquiv v)
    (IntegralTensor.tensorEquiv_one_tmul v) Y n j hj p q
  let : TopologicalSpace (RingPoint (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletionIntegers K)) :=
    schemePointTopology (𝓞 K)
      (affineChartWeilRestriction (𝓞 K) (𝓞 L) Y)
      (v.adicCompletionIntegers K)
  let : ∀ q : FinitePlacesAbove L v, TopologicalSpace
      (RingPoint (𝓞 L) Y (q.1.adicCompletionIntegers L)) :=
    fun q => schemePointTopology (𝓞 L) Y (q.1.adicCompletionIntegers L)
  have hh : numberFieldIntegralWeilRestrictionPointHomeomorph K L v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
        (IntegralTensor.tensorEquiv v)
        (IntegralTensor.tensorEquiv_one_tmul v) Y n j hj := rfl
  rw [hh]
  exact h

end Langlands.AlgebraicGeometry.PointTopology
