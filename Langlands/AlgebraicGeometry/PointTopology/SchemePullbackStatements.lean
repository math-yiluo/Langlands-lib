import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Fibre products for the actual scheme point topology -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- The actual point comparison of any relative limiting pullback cone is a
homeomorphism onto the compatible-pair subspace. -/
def SchemePointPullbackProperty
    [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S] : Prop :=
  ∀ (X Y Z : Over (Spec (CommRingCat.of R))) (f : X ⟶ Z) (g : Y ⟶ Z)
    (c : PullbackCone f g), IsLimit c →
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    @IsHomeomorph (RingPoint R c.pt S)
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g}
      (schemePointTopology R c.pt S) inferInstance
      (affineSchemePullbackPointComparison R S c)

end Langlands.AlgebraicGeometry.PointTopology
