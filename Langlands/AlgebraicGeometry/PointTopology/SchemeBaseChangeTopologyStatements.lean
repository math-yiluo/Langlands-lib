import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Topology comparison for actual nonaffine base change -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
variable [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
variable [TopologicalSpace A]

/-- The actual pullback-adjunction equivalence preserves the independently
constructed affine-chart final topologies for every relative scheme. -/
def SchemeBaseChangeTopologyProperty
    [IsTopologicalRing A] [IsLocalRing A] [IsOpenUnits A] : Prop :=
  ∀ X : Over (Spec (CommRingCat.of C)),
    letI : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
    letI : TopologicalSpace (RingPoint D (ringBaseChange C D X) A) :=
      schemePointTopology D (ringBaseChange C D X) A
    IsHomeomorph (ringPointBaseChangeEquiv C D A X)

end Langlands.AlgebraicGeometry.PointTopology
