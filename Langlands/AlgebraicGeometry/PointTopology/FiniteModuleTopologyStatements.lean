import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.Finiteness.Projective

/-! # Finite projective module topologies in Conrad Example 2.4 -/

noncomputable section

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The canonical module topology is the quotient topology for every finite
free presentation and the subspace topology for every split linear inclusion.
Finite projectivity supplies such a presentation and inclusion. -/
def FiniteProjectiveModuleTopologyProperties
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] : Prop :=
  (∀ (n : ℕ) (q : (Fin n → R) →ₗ[R] M), Function.Surjective q →
    moduleTopology R M = TopologicalSpace.coinduced q inferInstance) ∧
  (letI : TopologicalSpace M := moduleTopology R M
   ∀ (n : ℕ) (s : M →ₗ[R] Fin n → R) (p : (Fin n → R) →ₗ[R] M),
     p.comp s = LinearMap.id → IsEmbedding s) ∧
  (∃ (n : ℕ) (p : (Fin n → R) →ₗ[R] M) (s : M →ₗ[R] Fin n → R),
    Function.Surjective p ∧ Function.Injective s ∧ p.comp s = LinearMap.id)

end Langlands.AlgebraicGeometry.PointTopology
