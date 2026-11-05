import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

open Filter
open scoped Topology

namespace Langlands.Analysis

universe uG uE

/-- The actual equivariant Hilbert sum supplied by compact symmetric strong
approximations preserving every closed invariant subspace. -/
def CompactApproximationHilbertSumStatement : Prop := by
  classical
  exact
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
            ∃ (U : lp (fun P : A => ↥P.1) 2 ≃ₗᵢ[ℂ] W),
              (∀ v, HasSum (fun P : A => (v P : E)) (U v : E)) ∧
              (∀ (P : A) (x : P.1), (U (lp.single 2 P x) : E) = x) ∧
              ∃ (ρ : G →* (lp (fun P : A => ↥P.1) 2 →L[ℂ]
                  lp (fun P : A => ↥P.1) 2)),
                (∀ (g : G) v (P : A), ((ρ g v) P : E) = π g (v P)) ∧
                (∀ (g : G) v, (U (ρ g v) : E) = π g (U v)) ∧
                ∀ (g : G) v w,
                  inner ℂ (ρ g v) (ρ g w) = inner ℂ v w

end Langlands.Analysis
