import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Coefficient change for actual scheme points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable [TopologicalSpace S] [TopologicalSpace T]

/-- Continuous coefficient maps are continuous for the affine-chart final topologies. -/
def SchemeCoefficientContinuityProperty : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (f : S →ₐ[R] T), Continuous f →
    Continuous[schemePointTopology R X S, schemePointTopology R X T]
      (RingPoint.changeRing (X := X) f)

/-- Open coefficient embeddings give open maps for locally finite-type schemes. -/
def SchemeCoefficientOpenProperty
    [IsLocalRing S] [IsLocalRing T] [IsTopologicalRing S] [IsTopologicalRing T]
    [IsOpenUnits T] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom]
    (f : S →ₐ[R] T), IsOpenEmbedding f →
    @IsOpenMap (RingPoint R X S) (RingPoint R X T)
      (schemePointTopology R X S) (schemePointTopology R X T)
      (RingPoint.changeRing (X := X) f)

/-- Coefficient continuity and separately qualified openness on actual scheme points. -/
def SchemeCoefficientProperties : Prop :=
  SchemeCoefficientContinuityProperty R S T ∧
    (∀ [IsLocalRing S] [IsLocalRing T] [IsTopologicalRing S] [IsTopologicalRing T]
      [IsOpenUnits T], SchemeCoefficientOpenProperty R S T)

end Langlands.AlgebraicGeometry.PointTopology
