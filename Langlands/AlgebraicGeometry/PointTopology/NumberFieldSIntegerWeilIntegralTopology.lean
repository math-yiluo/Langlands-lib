import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.Global.AdelicFunctoriality.IntegralTopology
import Langlands.Global.NumberFieldSIntegerLocalTensor

/-! # Integral Weil point topology for actual global number-field S-integer models -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension IntegralTensor IntegralTopology
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldPlaceIntegralTensor
  Langlands.Global.NumberFieldSIntegerLocalTensor

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
  (S : Finset (FinitePlace K)) (v : HeightOneSpectrum (𝓞 K)) [Fact (v ∉ S)]
  (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))) [LocallyOfFiniteType Y.hom]

/-- Integral points of the actual relative Weil scheme are homeomorphic to
all original upper completed-integer points, for a projectively immersed model. -/
def numberFieldSIntegerWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom) :
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
        (v.adicCompletionIntegers K)) :=
      schemePointTopology ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
        (v.adicCompletionIntegers K)
    letI : ∀ q : FinitePlacesAbove L v, TopologicalSpace
        (RingPoint (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)) :=
      fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)
    RingPoint ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
        (v.adicCompletionIntegers K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoint (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)) := by
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
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (v.adicCompletionIntegers K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L) Y n j hj

/-- Each integral upper component is the original relative Weil counit along
the corresponding actual completed-integer factor test spectrum. -/
theorem numberFieldSIntegerWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
      (v.adicCompletionIntegers K))
    (q : FinitePlacesAbove L v) :
    numberFieldSIntegerWeilRestrictionPointHomeomorph K L S v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (v.adicCompletionIntegers K)
          (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
          (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
          (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L) q ≫
        affineChartWeilRestrictionComparison ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y
          (ringTest ((S : Set (FinitePlace K)).integer K) (v.adicCompletionIntegers K)) p := by
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
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (v.adicCompletionIntegers K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L) Y n j hj p q
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
      (v.adicCompletionIntegers K)) :=
    schemePointTopology ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
      (v.adicCompletionIntegers K)
  let : ∀ q : FinitePlacesAbove L v, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)) :=
    fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)
  have hh : numberFieldSIntegerWeilRestrictionPointHomeomorph K L S v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (v.adicCompletionIntegers K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
        (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
        (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L) Y n j hj := rfl
  rw [hh]
  exact h

end Langlands.AlgebraicGeometry.PointTopology
