import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates

/-!
# Topology comparison under actual affine base change
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The actual pullback-adjunction equivalence preserves the independent
global-section evaluation topologies on affine relative point spaces. -/
def AffineBaseChangeTopologyStatement : Prop :=
  ∀ (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
    [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left],
    IsHomeomorph (ringPointBaseChangeEquiv C D A X)

end Langlands.AlgebraicGeometry.PointTopology
