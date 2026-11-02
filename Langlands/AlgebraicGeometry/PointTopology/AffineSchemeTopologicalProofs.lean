import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologicalStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# Topological proofs for actual affine scheme points
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

theorem affineSchemeHausdorff_proof [T2Space S] :
    AffineSchemeHausdorffProperty R S := by
  intro X _
  exact (affineSchemePointHomeomorph R X S).isEmbedding.t2Space

theorem affineSchemeLocalCompactness_proof
    [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] :
    AffineSchemeLocalCompactnessProperty R S := by
  intro X _ _
  let : LocallyCompactSpace (AlgPoint R (AffineCoordinateRing R X) S) :=
    affineLocalCompactness_proof R (AffineCoordinateRing R X) S inferInstance
  exact (affineSchemePointHomeomorph R X S).isClosedEmbedding.locallyCompactSpace

theorem affineSchemeTopologicalProperties_proof :
    AffineSchemeTopologicalProperties R S := by
  constructor
  · intro _
    exact affineSchemeHausdorff_proof R S
  · intro _ _ _
    exact affineSchemeLocalCompactness_proof R S

end Langlands.AlgebraicGeometry.PointTopology
