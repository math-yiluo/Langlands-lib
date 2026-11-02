import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyBinaryUniqueness

/-!
# Uniqueness of the affine evaluation topology
-/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

theorem affineTopologyUniqueness_proof : AffineTopologyUniquenessProperty R S := by
  intro T hT
  exact affineTopology_eq_evaluation_of_pushouts R S T hT.1 hT.2.1 hT.2.2.1 hT.2.2.2

end Langlands.AlgebraicGeometry.PointTopology
