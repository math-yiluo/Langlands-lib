import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyAxioms
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Uniqueness of the topology on actual nonaffine points
-/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The source axioms force the named affine-chart topology on all locally
finite type actual relative scheme-point spaces. This is a uniqueness target. -/
def SchemePointTopologyUniquenessProperty
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S] : Prop :=
  ∀ T : SchemePointTopologyFamily R S, SchemePointTopologyAxioms R S T →
    T = evaluationSchemePointTopologyFamily R S

end Langlands.AlgebraicGeometry.PointTopology
