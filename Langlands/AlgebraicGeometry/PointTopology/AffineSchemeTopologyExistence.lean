import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyTransport
import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyExistence

/-!
# Existence of the evaluation topology on actual affine scheme points
-/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

theorem affineSchemeTopologyExistence_proof :
    AffineSchemeTopologyExistenceProperty R S := by
  have h := algebraTopology_toSchemes_axioms R S (evaluationAffineTopologyFamily R S)
    (affineTopologyExistence_proof R S)
  rw [evaluationAlgebraTopology_toSchemes] at h
  exact h

end Langlands.AlgebraicGeometry.PointTopology
