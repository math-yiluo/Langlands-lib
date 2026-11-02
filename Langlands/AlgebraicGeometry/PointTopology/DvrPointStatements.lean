import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Affine integral points over a discrete valuation ring
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped WithZero

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual finite-type affine integral points embed as an open and closed
subspace of fraction-field points, with the canonical valuation topologies. -/
def DvrAffinePointProperties : Prop :=
  letI : Valued K ℤᵐ⁰ := Valued.mk' ((IsDiscreteValuationRing.maximalIdeal R).valuation K)
  letI : TopologicalSpace R := TopologicalSpace.induced (algebraMap R K) inferInstance
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom],
      IsOpenEmbedding (RingPoint.changeRing (X := X) (Algebra.ofId R K)) ∧
      IsClosedEmbedding (RingPoint.changeRing (X := X) (Algebra.ofId R K))

end Langlands.AlgebraicGeometry.PointTopology
