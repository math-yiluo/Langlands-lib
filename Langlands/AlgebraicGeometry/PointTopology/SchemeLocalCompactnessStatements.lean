import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Local compactness of locally finite type scheme points
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Locally finite type actual scheme-point spaces are locally compact over a
Hausdorff locally compact local value ring with open units and continuous inversion. -/
def SchemePointLocalCompactnessProperty
    [IsLocalRing S] [IsTopologicalRing S] [IsOpenUnits S]
    [T2Space S] [LocallyCompactSpace S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom],
    @LocallyCompactSpace (RingPoint R X S) (schemePointTopology R X S)

end Langlands.AlgebraicGeometry.PointTopology
