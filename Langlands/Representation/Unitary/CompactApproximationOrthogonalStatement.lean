import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Filter
open scoped Topology

namespace Langlands.Analysis

universe uG uE

/-- Compact symmetric approximations produce a dense orthogonal family of
actual minimal nonzero closed invariant submodules. -/
def CompactApproximationOrthogonalStatement : Prop :=
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
      ∀ (W : Submodule ℂ E), IsClosed (W : Set E) →
        (∀ (g : G), ∀ x ∈ W, π g x ∈ W) →
        ∃ (A : Set (Submodule ℂ E)),
          (∀ P ∈ A, P ≤ W ∧ P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
            (∀ (g : G), ∀ x ∈ P, π g x ∈ P) ∧
            ∀ (Q : Submodule ℂ E), Q ≤ P → IsClosed (Q : Set E) →
              (∀ (g : G), ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
          A.Pairwise (fun P Q => P ⟂ Q) ∧
          (sSup A).topologicalClosure = W

end Langlands.Analysis
