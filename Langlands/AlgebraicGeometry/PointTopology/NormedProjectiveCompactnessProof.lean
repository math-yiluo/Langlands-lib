import Langlands.AlgebraicGeometry.PointTopology.NormedProjectiveCompactnessStatements
import Langlands.AlgebraicGeometry.ProjectiveSpace.BoundedCharts
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Mathlib.Analysis.Normed.Field.ProperSpace

/-! # Compactness of projective points from bounded affine charts -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization Topology
open Langlands.AlgebraicGeometry.PointTopology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

local instance (K : Type u) [Field K] (n : ℕ) (j : Fin (n + 1)) :
    Algebra K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway K n j

section LocallyCompactField

variable (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K] (n : ℕ)

theorem isCompact_boundedChart (j : Fin (n + 1)) :
    IsCompact (boundedChart K n j) := by
  let : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have he := finiteCoordinateClosedEmbedding_proof K
    (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)) K
    (n + 1) (_root_.AlgebraicGeometry.ProjSpace.ratio K n j)
    (_root_.AlgebraicGeometry.ProjSpace.adjoin_range_ratio K n j)
  have hc : IsCompact (Set.pi Set.univ
      (fun _ : Fin (n + 1) => Metric.closedBall (0 : K) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall (0 : K) 1)
  convert he.isCompact_preimage hc using 1
  ext p
  simp [boundedChart, Set.mem_pi, dist_zero_right]

theorem isCompact_boundedChartImage (j : Fin (n + 1)) :
    @IsCompact _ (schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K)
      (boundedChartImage K n j) := by
  let : TopologicalSpace (RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K) :=
    schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K
  exact (isCompact_boundedChart K n j).image (continuous_relativeChartPoint K n j)

end LocallyCompactField

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.AlgebraicGeometry.ProjectiveSpace

/-- Actual projective point spaces over locally compact nontrivially normed fields are compact. -/
theorem normedProjectivePointCompactness_proof
    (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K] :
    NormedProjectivePointCompactnessProperty K := by
  intro n
  let : TopologicalSpace (RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K) :=
    schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K
  refine ⟨?_⟩
  rw [← iUnion_boundedChartImage K n]
  exact isCompact_iUnion (isCompact_boundedChartImage K n)

end Langlands.AlgebraicGeometry.PointTopology
