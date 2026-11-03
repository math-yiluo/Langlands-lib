import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateEvaluation
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.Field

/-! # Bounded charts of actual projective point spaces -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization Topology
open Langlands.AlgebraicGeometry.PointTopology

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

local instance (K : Type u) [Field K] (n : ℕ) (j : Fin (n + 1)) :
    Algebra K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway K n j

section Field

variable (K : Type u) [Field K] (n : ℕ)

/-- The actual affine chart inclusion, as a morphism over the coefficient field. -/
def relativeChartInclusion (j : Fin (n + 1)) :
    ringTest K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j)) ⟶ Over.mk (projectiveSpaceToSpec K n) :=
  Over.homMk ((affineOpenCover K n).openCover.f j)
    (affineOpenCover_comp_toSpec K n j)

/-- The relative projective point obtained from an actual chart algebra map. -/
def relativeChartPoint (j : Fin (n + 1))
    (p : AlgPoint K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j)) K) :
    RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K :=
  ringTestMap K p.toAlgHom ≫ relativeChartInclusion K n j

@[simp]
theorem relativeChartPoint_left (j : Fin (n + 1))
    (p : AlgPoint K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j)) K) :
    (relativeChartPoint K n j p).left = chartPoint n j p.toAlgHom := rfl

theorem continuous_relativeChartPoint [TopologicalSpace K]
    [ContinuousMul K] [IsOpenUnits K] (j : Fin (n + 1)) :
    Continuous[inferInstance,
      schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K]
      (relativeChartPoint K n j) := by
  let : TopologicalSpace (RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K) :=
    schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K
  have he : (fun p : AlgPoint K
      (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)) K =>
        ringTestMap K p.toAlgHom) =
      (spectrumAlgebraPointHomeomorph K K
        (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j))).symm := by
    rfl
  have hc := (continuous_affineToSchemePointMap K K (relativeChartInclusion K n j)).comp
    (spectrumAlgebraPointHomeomorph K K
      (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X j))).symm.continuous
  rw [← he] at hc
  exact hc

end Field

section NormedField

variable (K : Type u) [NormedField K] (n : ℕ)

/-- Chart algebra points whose homogeneous-coordinate ratios have norm at most one. -/
def boundedChart (j : Fin (n + 1)) :
    Set (AlgPoint K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j)) K) :=
  {p | ∀ k, ‖p (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k)‖ ≤ 1}

/-- The actual projective points represented by the bounded part of a chart. -/
def boundedChartImage (j : Fin (n + 1)) :
    Set (RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K) :=
  relativeChartPoint K n j '' boundedChart K n j

/-- Choosing a coordinate of maximal norm represents every point in a bounded chart. -/
theorem exists_mem_boundedChartImage
    (p : RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K) :
    ∃ j, p ∈ boundedChartImage K n j := by
  classical
  have hp : p.left ≫ projectiveSpaceToSpec K n = 𝟙 (Spec (CommRingCat.of K)) := by
    have hw : p.left ≫ projectiveSpaceToSpec K n =
        Spec.map (CommRingCat.ofHom (algebraMap K K)) := Over.w p
    change p.left ≫ projectiveSpaceToSpec K n =
      Spec.map (𝟙 (CommRingCat.of K)) at hw
    simpa using hw
  let a := pointCoordinates n p.left hp
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖a i‖) Finset.univ_nonempty
  have hpos : 0 < ‖a j‖ := by
    have hmax := hj (pointChartIndex n p.left hp) (Finset.mem_univ _)
    have hone : a (pointChartIndex n p.left hp) = 1 := pointCoordinates_index n p.left hp
    rw [hone, norm_one] at hmax
    exact lt_of_lt_of_le zero_lt_one hmax
  have hj0 : a j ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨j, AlgPoint.ofAlgHom (coordinateChartMap n a j hj0), ?_, ?_⟩
  · intro k
    change ‖coordinateChartMap n a j hj0
      (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k)‖ ≤ 1
    rw [coordinateChartMap_ratio, norm_div]
    exact (div_le_one hpos).mpr (hj k (Finset.mem_univ _))
  · apply RingPoint.ext
    exact chartPoint_coordinateChartMap n p.left hp j hj0

theorem iUnion_boundedChartImage :
    ⋃ j, boundedChartImage K n j = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨j, hj⟩ := exists_mem_boundedChartImage K n p
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

end NormedField

end Langlands.AlgebraicGeometry.ProjectiveSpace
