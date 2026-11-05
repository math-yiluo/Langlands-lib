import Mathlib.Analysis.InnerProductSpace.Spectrum

open Filter
open scoped Topology

namespace Langlands.Analysis

universe uG uE

/-- Compact symmetric strong approximations give finite multiplicity in an
orthogonal family when actual unitary intertwiners also intertwine the
approximating operators. -/
def CompactApproximationMultiplicityStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)),
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
    ∀ (T : ℕ → E →L[ℂ] E),
      (∀ n, IsCompactOperator (T n)) →
      (∀ n, (T n).IsSymmetric) →
      (∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) →
      ∀ (hpres : ∀ (n : ℕ) (S : Submodule ℂ E), IsClosed (S : Set E) →
        (∀ (g : G), ∀ x ∈ S, π g x ∈ S) → ∀ x ∈ S, T n x ∈ S),
        (∀ (P Q : Submodule ℂ E) (hPc : IsClosed (P : Set E))
          (hPi : ∀ (g : G), ∀ x ∈ P, π g x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
          (∀ (g : G) (x : P), (U ⟨π g x, hPi g x x.2⟩ : E) = π g (U x)) →
          ∀ (n : ℕ) (x : P),
            (U ⟨T n x, hpres n P hPc hPi x x.2⟩ : E) = T n (U x)) →
        ∀ (A : Set (Submodule ℂ E))
          (hA : ∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
            ∀ (g : G), ∀ x ∈ P, π g x ∈ P),
          A.Pairwise (fun P Q => P ⟂ Q) →
          ∀ (P : Submodule ℂ E) (hP : P ∈ A),
            {Q : Submodule ℂ E | Q ∈ A ∧
              ∃ (U : P ≃ₗᵢ[ℂ] Q), ∀ (g : G) (x : P),
                (U ⟨π g x, (hA P hP).2.2 g x x.2⟩ : E) = π g (U x)}.Finite

end Langlands.Analysis
