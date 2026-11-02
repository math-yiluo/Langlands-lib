import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-!
# Coefficient change on actual affine scheme points
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable [TopologicalSpace S] [TopologicalSpace T]

/-- A continuous change of value algebra is continuous on actual affine points. -/
def AffineSchemeCoefficientContinuityProperty : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (f : S →ₐ[R] T), Continuous f →
      Continuous (RingPoint.changeRing (X := X) f)

/-- Embeddings and closed embeddings of value algebras give the same
properties on actual points of every affine scheme. -/
def AffineSchemeCoefficientEmbeddingProperties : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (f : S →ₐ[R] T),
      (IsEmbedding f → IsEmbedding (RingPoint.changeRing (X := X) f)) ∧
      (IsClosedEmbedding f → IsClosedEmbedding (RingPoint.changeRing (X := X) f))

/-- For affine schemes locally of finite type, open coefficient embeddings
give open point embeddings. -/
def AffineSchemeCoefficientOpenProperty
    [IsTopologicalRing S] [IsTopologicalRing T] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] (f : S →ₐ[R] T), IsOpenEmbedding f →
      IsOpenEmbedding (RingPoint.changeRing (X := X) f)

/-- Finite-type actual affine points over a discrete topological ring are discrete. -/
def AffineSchemeDiscreteProperty [IsTopologicalRing S] [DiscreteTopology S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom], DiscreteTopology (RingPoint R X S)

/-- The coefficient-change and discreteness conclusions with separate hypotheses. -/
def AffineSchemeCoefficientProperties : Prop :=
  AffineSchemeCoefficientContinuityProperty R S T ∧
    AffineSchemeCoefficientEmbeddingProperties R S T ∧
    (∀ [IsTopologicalRing S] [IsTopologicalRing T],
      AffineSchemeCoefficientOpenProperty R S T) ∧
    (∀ [IsTopologicalRing S] [DiscreteTopology S], AffineSchemeDiscreteProperty R S)

end Langlands.AlgebraicGeometry.PointTopology
