import Langlands.Representation.Filtration.ObjectDefinitions

/-! A lattice-theoretic criterion for matching composition factors of two
representations whose subrepresentations carry strictly monotone counts bounded
by two. -/

namespace Langlands

/-- Let `ρ` and `σ` be representations of a monoid over a field. Suppose that
their invariant subspaces carry strictly monotone natural counts `μ` and `ν`,
vanishing at zero and at most two on the whole space. Suppose also that there
are nonzero intertwining maps `A : ρ → σ` and `A' : σ → ρ` along which the
counts add up, and that either map being nonzero on a subspace of count one
forces `ρ` and `σ` to be equivalent. Then `ρ` and `σ` have the same
composition factors with multiplicities. This declaration states the internal
algebraic step of Bernstein–Zelevinsky 1977, §2.16(1); it does not prove it. -/
def LengthTwoFactorMatchingCriterion.{uK, uG, uV, uW} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (V : Type uV) [AddCommGroup V] [Module k V]
    (W : Type uW) [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    (μ : Subrepresentation ρ → ℕ) (ν : Subrepresentation σ → ℕ),
    StrictMono μ → StrictMono ν → μ ⊥ = 0 → ν ⊥ = 0 → μ ⊤ ≤ 2 → ν ⊤ ≤ 2 →
    ∀ (A : ρ.IntertwiningMap σ) (A' : σ.IntertwiningMap ρ), A ≠ 0 → A' ≠ 0 →
      μ ⊤ = μ A.ker + ν A.range → ν ⊤ = ν A'.ker + μ A'.range →
      (∀ S : Subrepresentation ρ, μ S = 1 → (∃ v ∈ S, A v ≠ 0) →
        Nonempty (ρ.Equiv σ)) →
      (∀ S' : Subrepresentation σ, ν S' = 1 → (∃ w ∈ S', A' w ≠ 0) →
        Nonempty (ρ.Equiv σ)) →
      HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ)

end Langlands
