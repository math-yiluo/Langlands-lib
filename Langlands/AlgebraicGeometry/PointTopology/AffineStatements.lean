import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Finite-coordinate statements for affine point topologies

These are proposition-valued targets for the finite-coordinate and local-compactness
parts of Conrad's Proposition 2.1. They assert properties of the actual algebra-map
point spaces and their previously constructed evaluation topologies.
-/

universe u v w

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (A : Type v) (S : Type w)
variable [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
variable [TopologicalSpace S]

/-- Evaluation on any finite algebra-generating family is a topological embedding. -/
def FiniteCoordinateEmbedding [IsTopologicalRing S] : Prop :=
  ∀ (n : ℕ) (a : Fin n → A), Algebra.adjoin R (Set.range a) = ⊤ →
    IsEmbedding (fun (p : AlgPoint R A S) (i : Fin n) => p (a i))

/-- Over a Hausdorff coefficient ring the finite-coordinate image is closed. -/
def FiniteCoordinateClosedEmbedding [IsTopologicalRing S] [T2Space S] : Prop :=
  ∀ (n : ℕ) (a : Fin n → A), Algebra.adjoin R (Set.range a) = ⊤ →
    IsClosedEmbedding (fun (p : AlgPoint R A S) (i : Fin n) => p (a i))

/-- Finite-type affine points over a Hausdorff locally compact coefficient ring
are locally compact. No topology on the base algebra is assumed. -/
def AffineLocalCompactness [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] : Prop :=
  Algebra.FiniteType R A → LocallyCompactSpace (AlgPoint R A S)

/-- The finite-coordinate assertions and their local-compactness consequence,
with the Hausdorff and local-compactness hypotheses attached only where needed. -/
def AffineCoordinateProperties [IsTopologicalRing S] : Prop :=
  FiniteCoordinateEmbedding R A S ∧
    (∀ [T2Space S], FiniteCoordinateClosedEmbedding R A S) ∧
    (∀ [T2Space S] [LocallyCompactSpace S], AffineLocalCompactness R A S)

end Langlands.AlgebraicGeometry.PointTopology
