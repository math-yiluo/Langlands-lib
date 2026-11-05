import Mathlib.Analysis.InnerProductSpace.Spectrum

open Filter
open scoped Topology

namespace Langlands.Analysis

universe u

/-- A strongly convergent compact symmetric approximation to the identity
detects a nonzero finite-dimensional eigenspace in every supplied nonzero
closed submodule preserved by all the approximating operators. -/
def CompactApproximationEigenspaceStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℕ → E →L[ℂ] E),
    (∀ n, IsCompactOperator (T n)) →
    (∀ n, (T n).IsSymmetric) →
    (∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) →
    ∀ (W : Submodule ℂ E), W ≠ ⊥ → IsClosed (W : Set E) →
      (∀ n, ∀ x ∈ W, T n x ∈ W) →
      ∃ (n : ℕ) (μ : ℂ), μ ≠ 0 ∧
        W ⊓ Module.End.eigenspace (T n).toLinearMap μ ≠ ⊥ ∧
        FiniteDimensional ℂ
          (W ⊓ Module.End.eigenspace (T n).toLinearMap μ : Submodule ℂ E)

end Langlands.Analysis
