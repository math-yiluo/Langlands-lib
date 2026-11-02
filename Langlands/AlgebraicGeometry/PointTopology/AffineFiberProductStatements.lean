import Langlands.AlgebraicGeometry.PointTopology.AffineFiberProducts
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The affine fibre-product topology statement
-/

noncomputable section

universe u

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The actual affine fibre-product point comparison has the subspace product topology. -/
def AffineFiberProductTopologyProperty (R C A B S : Type u)
    [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R C] [Algebra R A] [Algebra R B] [Algebra R S]
    [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  IsHomeomorph (specFiberProductPointPairEquiv R C A B S)

end Langlands.AlgebraicGeometry.PointTopology
