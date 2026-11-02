import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Hausdorffness and local compactness of actual affine scheme points
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Hausdorff value rings give Hausdorff actual points of every affine scheme.
No finite-type or topological-ring hypothesis is needed. -/
def AffineSchemeHausdorffProperty [T2Space S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left],
    T2Space (RingPoint R X S)

/-- Finite-type affine scheme points over a Hausdorff locally compact
topological value algebra are locally compact. -/
def AffineSchemeLocalCompactnessProperty
    [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom], LocallyCompactSpace (RingPoint R X S)

/-- The two topological conclusions retain their separate hypotheses. -/
def AffineSchemeTopologicalProperties : Prop :=
  (∀ [T2Space S], AffineSchemeHausdorffProperty R S) ∧
    (∀ [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S],
      AffineSchemeLocalCompactnessProperty R S)

end Langlands.AlgebraicGeometry.PointTopology
