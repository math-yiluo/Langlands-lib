import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.RingTheory.Noetherian.Defs

/-! # Nonzero invariants for Noetherian étale equivalence relations -/

universe u

namespace Langlands.AlgebraicGeometry

/-- For a ring étale equivalence relation over a Noetherian ring, acyclicity of
all coactions implies that every nonzero coaction has a nonzero invariant. -/
def GroupoidCoactionNonzeroInvariantStatement : Prop :=
  ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (t : B →+* C), RingEtaleEquivalenceRelation t → IsNoetherianRing B →
    (∀ (K : Type u) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic) →
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Nontrivial M]
      (θ : GroupoidCoaction t M), ∃ m : M, m ∈ θ.invariants ∧ m ≠ 0

end Langlands.AlgebraicGeometry
