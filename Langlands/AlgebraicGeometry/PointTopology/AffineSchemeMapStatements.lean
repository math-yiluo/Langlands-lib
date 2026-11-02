import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Mapping properties on actual affine scheme points
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
variable [TopologicalSpace S]

/-- Every actual affine scheme morphism over the base induces a continuous
postcomposition map on relative points. -/
def AffineSchemeContinuityProperty : Prop :=
  ∀ f : X ⟶ Y, Continuous (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S))

/-- A closed immersion gives an embedding on actual relative points.
Hausdorffness of the value ring gives closedness as a separate conclusion. -/
def AffineSchemeClosedImmersionProperties : Prop :=
  ∀ f : X ⟶ Y, ∀ [IsClosedImmersion f.left],
    IsEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) ∧
      (∀ [T2Space S], IsClosedEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)))

/-- The continuity and closed-immersion assertions for actual affine scheme
point spaces with their global-section evaluation topologies. -/
def AffineSchemeMapProperties : Prop :=
  AffineSchemeContinuityProperty R S X Y ∧
    AffineSchemeClosedImmersionProperties R S X Y

end Langlands.AlgebraicGeometry.PointTopology
