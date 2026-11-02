import Langlands.AlgebraicGeometry.PointTopology.AffineScheme

/-!
# Affine points over a product of value rings

The actual relative point map is a homeomorphism for the evaluation topologies.
This is a derived generalization of the affine topology assertion in Conrad's
Theorem 3.6, formula (3.6.1).
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Evaluation topology commutes with arbitrary products of value algebras. -/
def AffineProductRingTopologyStatement : Prop :=
  ∀ (C : Type u) [CommRing C] (ι : Type u) (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    [∀ i, TopologicalSpace (R i)]
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left],
    IsHomeomorph (productPointMap C R X)

end Langlands.AlgebraicGeometry.PointTopology
