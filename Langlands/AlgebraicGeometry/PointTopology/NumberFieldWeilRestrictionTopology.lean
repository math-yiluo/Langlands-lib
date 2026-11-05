import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology

/-! # Actual all-upper-place Weil point homeomorphisms for number fields -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open NumberField IsDedekindDomain
open Langlands.Global.AdelicFunctoriality
open scoped NumberField NumberField.LiesOver FiniteExtension InfiniteExtension

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (Y : Over (Spec (CommRingCat.of L))) [LocallyOfFiniteType Y.hom]

section FinitePlace

variable (v : HeightOneSpectrum (𝓞 K))

private theorem finitePlaceFactorIsModuleTopology (q : FinitePlacesAbove L v) :
    IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) := by
  let : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- At any finite number-field place, actual points of a quasi-projective
Weil scheme are homeomorphic to the product over all upper completions. -/
def finitePlaceWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom) :
    letI : TopologicalSpace
        (RingPoint K (affineChartWeilRestriction K L Y) (v.adicCompletion K)) :=
      schemePointTopology K (affineChartWeilRestriction K L Y) (v.adicCompletion K)
    letI : ∀ q : FinitePlacesAbove L v,
        TopologicalSpace (RingPoint L Y (q.1.adicCompletion L)) :=
      fun q => schemePointTopology L Y (q.1.adicCompletion L)
    RingPoint K (affineChartWeilRestriction K L Y) (v.adicCompletion K) ≃ₜ
      (∀ q : FinitePlacesAbove L v, RingPoint L Y (q.1.adicCompletion L)) := by
  letI : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    finitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    K L (v.adicCompletion K) (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (finitePlaceTensorEquiv K L v) (finitePlaceTensorEquiv_one_tmul K L v) Y n j hj

/-- Every finite upper-place component is the original Weil counit
evaluated on the actual completed-tensor factor test spectrum. -/
theorem finitePlaceWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom)
    (p : RingPoint K (affineChartWeilRestriction K L Y) (v.adicCompletion K))
    (q : FinitePlacesAbove L v) :
    finitePlaceWeilRestrictionPointHomeomorph K L Y v n j hj p q =
      completedTensorWeilRestrictionFactorTestMap K L (v.adicCompletion K)
          (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
          (finitePlaceTensorEquiv K L v) (finitePlaceTensorEquiv_one_tmul K L v) q ≫
        affineChartWeilRestrictionComparison K L Y (ringTest K (v.adicCompletion K)) p := by
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    finitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    K L (v.adicCompletion K) (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (finitePlaceTensorEquiv K L v) (finitePlaceTensorEquiv_one_tmul K L v) Y n j hj p q

end FinitePlace

section InfinitePlace

variable (v : InfinitePlace K)

omit [NumberField K] in
private theorem infinitePlaceFactorIsModuleTopology (q : InfinitePlacesAbove L v) :
    IsModuleTopology v.Completion q.1.Completion := by
  let := infiniteCompletionNontriviallyNormedField v
  exact isModuleTopologyOfFiniteDimensional

/-- At any infinite number-field place, including both real and complex
cases, the original Weil points identify homeomorphically with all upper points. -/
def infinitePlaceWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom) :
    letI : TopologicalSpace
        (RingPoint K (affineChartWeilRestriction K L Y) v.Completion) :=
      schemePointTopology K (affineChartWeilRestriction K L Y) v.Completion
    letI : ∀ q : InfinitePlacesAbove L v, TopologicalSpace (RingPoint L Y q.1.Completion) :=
      fun q => schemePointTopology L Y q.1.Completion
    RingPoint K (affineChartWeilRestriction K L Y) v.Completion ≃ₜ
      (∀ q : InfinitePlacesAbove L v, RingPoint L Y q.1.Completion) := by
  letI : ∀ q : InfinitePlacesAbove L v, IsModuleTopology v.Completion q.1.Completion :=
    infinitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    K L v.Completion (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (infiniteTensorEquiv v) (infiniteTensorMap_one_tmul v) Y n j hj

/-- Every infinite upper-place component retains the original counit and
the actual completion embedding through the completed-tensor factor test. -/
theorem infinitePlaceWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom)
    (p : RingPoint K (affineChartWeilRestriction K L Y) v.Completion)
    (q : InfinitePlacesAbove L v) :
    infinitePlaceWeilRestrictionPointHomeomorph K L Y v n j hj p q =
      completedTensorWeilRestrictionFactorTestMap K L v.Completion
          (fun q : InfinitePlacesAbove L v => q.1.Completion)
          (infiniteTensorEquiv v) (infiniteTensorMap_one_tmul v) q ≫
        affineChartWeilRestrictionComparison K L Y (ringTest K v.Completion) p := by
  let : ∀ q : InfinitePlacesAbove L v, IsModuleTopology v.Completion q.1.Completion :=
    infinitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    K L v.Completion (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (infiniteTensorEquiv v) (infiniteTensorMap_one_tmul v) Y n j hj p q

end InfinitePlace

end Langlands.AlgebraicGeometry.PointTopology
