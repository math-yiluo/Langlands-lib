import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyAxioms
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Existence of the canonical topology on actual scheme points -/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- The constructed affine-chart final topology satisfies all five source
axioms on actual points of locally finite type relative schemes. -/
def SchemePointTopologyExistenceProperty
    [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S] : Prop :=
  SchemePointTopologyAxioms R S (evaluationSchemePointTopologyFamily R S)

end Langlands.AlgebraicGeometry.PointTopology
