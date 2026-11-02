import Langlands.AlgebraicGeometry.PointTopology.LocalProductPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates

/-!
# Comparison with points of actual local base changes

The independent product-point hypotheses and the affine evaluation topology
are preserved when each target is written over its own value ring.
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The source-qualified product comparison with actual base-changed local models. -/
def LocalProductPointComparisonStatement : Prop :=
  ∀ (C : Type u) [CommRing C] (ι : Type u) (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    (X : Over (Spec (CommRingCat.of C))),
    (∀ [QuasiSeparatedSpace X.left],
      Function.Injective (localProductPointMap C R X)) ∧
    (∀ [IsAffine X.left],
      Function.Surjective (localProductPointMap C R X)) ∧
    (∀ [CompactSpace X.left] [∀ i, IsLocalRing (R i)],
      Function.Surjective (localProductPointMap C R X)) ∧
    (∀ [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
      [IsAffine X.left],
      IsHomeomorph (localProductPointMap C R X))

end Langlands.AlgebraicGeometry.PointTopology
