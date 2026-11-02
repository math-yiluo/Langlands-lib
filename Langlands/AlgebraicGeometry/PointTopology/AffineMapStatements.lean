import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Quotient and coefficient-map statements for affine point topologies

Prop-valued targets for the closed-immersion part of Conrad Proposition 2.1
and the change-of-ring assertions of Example 2.2.
-/

universe u v w x y

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (A : Type v) (B : Type w) (S : Type x) (T : Type y)
variable [CommRing R] [CommRing A] [CommRing B] [CommRing S] [CommRing T]
variable [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
variable [TopologicalSpace S] [TopologicalSpace T]

/-- A surjection of coordinate algebras gives an embedding on actual points,
and a closed embedding when the value ring is Hausdorff. -/
def QuotientPointEmbeddingProperties : Prop :=
  ∀ f : A →ₐ[R] B, Function.Surjective f →
    IsEmbedding (AlgPoint.precomp (S := S) f) ∧
      (∀ [T2Space S], IsClosedEmbedding (AlgPoint.precomp (S := S) f))

/-- Embedding and closed-embedding coefficient maps retain these properties on
affine point spaces, without finite generation or separation hypotheses. -/
def CoefficientEmbeddingProperties : Prop :=
  ∀ f : S →ₐ[R] T,
    (IsEmbedding f → IsEmbedding (AlgPoint.mapCoefficients (A := A) f)) ∧
    (IsClosedEmbedding f → IsClosedEmbedding (AlgPoint.mapCoefficients (A := A) f))

/-- Over topological rings, an open embedding of coefficients induces an open
embedding of points when the coordinate algebra is of finite type. -/
def CoefficientOpenEmbeddingProperty [IsTopologicalRing S] [IsTopologicalRing T] : Prop :=
  Algebra.FiniteType R A →
    ∀ f : S →ₐ[R] T, IsOpenEmbedding f →
      IsOpenEmbedding (AlgPoint.mapCoefficients (A := A) f)

/-- Finite-type affine points over a discrete topological value ring are discrete. -/
def AffineDiscreteProperty [IsTopologicalRing S] [DiscreteTopology S] : Prop :=
  Algebra.FiniteType R A → DiscreteTopology (AlgPoint R A S)

/-- The quotient, coefficient-change and discreteness assertions, with each
topological-ring and discreteness hypothesis scoped to its own assertion. -/
def AffineMapProperties : Prop :=
  QuotientPointEmbeddingProperties R A B S ∧
    CoefficientEmbeddingProperties R A S T ∧
    (∀ [IsTopologicalRing S] [IsTopologicalRing T],
      CoefficientOpenEmbeddingProperty R A S T) ∧
    (∀ [IsTopologicalRing S] [DiscreteTopology S], AffineDiscreteProperty R A S)

end Langlands.AlgebraicGeometry.PointTopology
