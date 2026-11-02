import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Closed-immersion properties of actual scheme point spaces
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Actual closed immersions give embeddings on the final point topologies,
and give closed embeddings when the value ring is Hausdorff. -/
def SchemePointClosedImmersionProperties
    [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left],
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    IsEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) ∧
      (∀ [T2Space S], IsClosedEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
        (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)))

end Langlands.AlgebraicGeometry.PointTopology
