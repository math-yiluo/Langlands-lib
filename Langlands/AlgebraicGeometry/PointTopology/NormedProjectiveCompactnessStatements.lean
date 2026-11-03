import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Compactness of actual projective points over locally compact normed fields -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The normed-field projective case of local proper-point compactness. -/
def NormedProjectivePointCompactnessProperty
    (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K] : Prop :=
  ∀ n : ℕ, @CompactSpace (RingPoint K (Over.mk (projectiveSpaceToSpec K n)) K)
    (schemePointTopology K (Over.mk (projectiveSpaceToSpec K n)) K)

end Langlands.AlgebraicGeometry.PointTopology
