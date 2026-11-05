import Mathlib.Analysis.InnerProductSpace.Spectrum

open Filter
open scoped Topology

namespace Langlands.Analysis

universe uG uE

/-- Compact symmetric approximations preserving closed subrepresentations force
every nonzero closed invariant subspace to contain a minimal one. -/
def CompactApproximationMinimalStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)),
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
    ∀ (T : ℕ → E →L[ℂ] E),
      (∀ n, IsCompactOperator (T n)) →
      (∀ n, (T n).IsSymmetric) →
      (∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) →
      (∀ (n : ℕ) (S : Submodule ℂ E), IsClosed (S : Set E) →
        (∀ (g : G), ∀ x ∈ S, π g x ∈ S) →
        ∀ x ∈ S, T n x ∈ S) →
      ∀ (W : Submodule ℂ E), W ≠ ⊥ → IsClosed (W : Set E) →
        (∀ (g : G), ∀ x ∈ W, π g x ∈ W) →
        ∃ (P : Submodule ℂ E), P ≤ W ∧ P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
          (∀ (g : G), ∀ x ∈ P, π g x ∈ P) ∧
          ∀ (Q : Submodule ℂ E), Q ≤ P → IsClosed (Q : Set E) →
            (∀ (g : G), ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P

end Langlands.Analysis
