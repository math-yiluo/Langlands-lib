import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyExistence
import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyUniqueness

/-!
# Characterization of the affine evaluation topology
-/

universe u v

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

theorem affineTopologyCharacterization_proof :
    AffineTopologyCharacterizationProperty R S := by
  intro T
  constructor
  · exact affineTopologyUniqueness_proof R S T
  · intro hT
    subst T
    exact affineTopologyExistence_proof R S

end Langlands.AlgebraicGeometry.PointTopology
