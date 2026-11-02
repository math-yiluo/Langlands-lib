import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Hausdorffness of separated scheme point spaces -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- A separated relative scheme has a Hausdorff actual point space over a
Hausdorff topological local value algebra with open units. -/
def SchemePointHausdorffProperty
    [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S] [T2Space S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom],
    @T2Space (RingPoint R X S) (schemePointTopology R X S)

end Langlands.AlgebraicGeometry.PointTopology
