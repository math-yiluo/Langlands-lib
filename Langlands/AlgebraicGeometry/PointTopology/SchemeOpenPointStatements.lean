import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Open-chart and functoriality properties of actual scheme point topologies
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Affine open subschemes of affine schemes induce open embeddings on actual points. -/
def AffineOpenPointProperty [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (U : X.left.Opens) [IsAffine U],
    IsOpenEmbedding (openPointMap R X S U)

/-- Every actual open subscheme induces an open embedding for the final point topologies. -/
def SchemeOpenPointProperty [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens),
    letI : TopologicalSpace (RingPoint R (openOver R X U) S) :=
      schemePointTopology R (openOver R X U) S
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    IsOpenEmbedding (openPointMap R X S U)

/-- Actual postcomposition is continuous for the affine-chart final point topologies. -/
def SchemePointContinuityProperty [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y),
    Continuous[schemePointTopology R X S, schemePointTopology R Y S]
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S))

/-- The open-chart and functoriality part of the local-ring gluing construction. -/
def SchemeOpenPointProperties [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] : Prop :=
  AffineOpenPointProperty R S ∧ SchemeOpenPointProperty R S ∧
    SchemePointContinuityProperty R S

end Langlands.AlgebraicGeometry.PointTopology
