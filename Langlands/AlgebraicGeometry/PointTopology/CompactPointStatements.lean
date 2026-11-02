import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of actual points over compact value rings
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Finite-type affine points over a compact Hausdorff topological value ring
are compact in the existing evaluation topology. -/
def AffineSchemeCompactnessProperty
    [IsTopologicalRing S] [T2Space S] [CompactSpace S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom], CompactSpace (RingPoint R X S)

/-- Quasi-compact locally finite type scheme points over a compact Hausdorff
local value ring are compact in the affine-chart final topology. -/
def SchemePointCompactnessProperty
    [IsTopologicalRing S] [T2Space S] [CompactSpace S] [IsLocalRing S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left],
      @CompactSpace (RingPoint R X S) (schemePointTopology R X S)

/-- The affine compactness result and its local-value-ring gluing consequence. -/
def CompactValueRingPointProperties
    [IsTopologicalRing S] [T2Space S] [CompactSpace S] : Prop :=
  AffineSchemeCompactnessProperty R S ∧
    ∀ [IsLocalRing S], SchemePointCompactnessProperty R S

end Langlands.AlgebraicGeometry.PointTopology
