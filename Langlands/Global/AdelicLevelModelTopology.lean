import Langlands.Global.AdelicLevelModelPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints

/-! # Product topology on actual adelic-level model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable [∀ i, TopologicalSpace (R i)]
variable (X : Over (Spec (CommRingCat.of C)))

/-- The product of independently constructed point topologies on the actual local models. -/
@[instance_reducible]
def localModelPointProductTopology :
    TopologicalSpace (∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i)) :=
  @Pi.topologicalSpace ι
    (fun i => RingPoint (R i) (ringBaseChange C (R i) X) (R i))
    (fun i => schemePointTopology (R i) (ringBaseChange C (R i) X) (R i))

/-- Pull the local-model product topology back along the original product-point map. -/
@[instance_reducible]
def localProductPointTopology :
    TopologicalSpace (RingPoint C X (∀ i, R i)) :=
  TopologicalSpace.induced (localProductPointMap C R X)
    (localModelPointProductTopology C R X)

/-- The product-point map is inducing by the definition of the source topology. -/
theorem localProductPointMap_isInducing :
    @IsInducing (RingPoint C X (∀ i, R i))
      (∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i))
      (localProductPointTopology C R X) (localModelPointProductTopology C R X)
      (localProductPointMap C R X) := by
  let := localModelPointProductTopology C R X
  let := localProductPointTopology C R X
  exact ⟨rfl⟩

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The actual curve-place level topology, induced by the original local-model map. -/
@[instance_reducible]
def curvePlaceLevelModelPointTopology :
    TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S)) :=
  TopologicalSpace.induced (curvePlaceLevelModelPointMap k F S X)
    (localModelPointProductTopology (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S) X)

/-- The explicit coefficient equivalence identifies the two induced constructions. -/
theorem curvePlaceLevelModelPointTopology_eq :
    curvePlaceLevelModelPointTopology k F S X =
      TopologicalSpace.induced
        (ringPointChangeRingEquiv (curvePlaceSIntegers k F S) X
          (curvePlaceLevelFactorAlgEquiv k F S))
        (localProductPointTopology (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F S) X) := by
  unfold curvePlaceLevelModelPointTopology localProductPointTopology
  rw [curvePlaceLevelModelPointMap_eq, induced_compose]

/-- The original arithmetic coordinate map is inducing for the defined topology. -/
theorem curvePlaceLevelModelPointMap_isInducing :
    @IsInducing (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (∀ i, RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
        (CurvePlaceLevelFactor k F S i))
      (curvePlaceLevelModelPointTopology k F S X)
      (localModelPointProductTopology (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S) X)
      (curvePlaceLevelModelPointMap k F S X) := by
  let := localModelPointProductTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F S) X
  let := curvePlaceLevelModelPointTopology k F S X
  exact ⟨rfl⟩

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The actual full number-field level topology, including every infinite factor. -/
@[instance_reducible]
def numberFieldLevelModelPointTopology :
    TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) :=
  TopologicalSpace.induced (numberFieldLevelModelPointMap K S X)
    (localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S) X)

/-- The explicit full-level coefficient equivalence identifies the induced constructions. -/
theorem numberFieldLevelModelPointTopology_eq :
    numberFieldLevelModelPointTopology K S X =
      TopologicalSpace.induced
        (ringPointChangeRingEquiv ((S : Set (FinitePlace K)).integer K) X
          (numberFieldLevelFactorAlgEquiv K S))
        (localProductPointTopology ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K S) X) := by
  unfold numberFieldLevelModelPointTopology localProductPointTopology
  rw [numberFieldLevelModelPointMap_eq, induced_compose]

/-- The original full-level coordinate map is inducing for the defined topology. -/
theorem numberFieldLevelModelPointMap_isInducing :
    @IsInducing
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (∀ i, RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
        (NumberFieldLevelFactor K S i))
      (numberFieldLevelModelPointTopology K S X)
      (localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S) X)
      (numberFieldLevelModelPointMap K S X) := by
  let := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K S) X
  let := numberFieldLevelModelPointTopology K S X
  exact ⟨rfl⟩

end NumberField

end Langlands.Global
