import Langlands.Analysis.HilbertSumTraceProof
import Langlands.TraceFormula.SmoothingEigenspaceHilbertSum
import Langlands.TraceFormula.SmoothingMomentFactorization

/-! # Finite local trace expansions on smoothing eigenspaces -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals
open scoped BigOperators

universe u v w

/-- If the positive-power traces of the compressions to Hilbert summands factor
in the test variable, the trace on each nonzero smoothing eigenspace is a finite
linear combination of the same functionals. -/
def FiniteSmoothingTraceExpansionStatement : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : Type v) (W : J → Submodule ℂ H) [∀ j, CompleteSpace (W j)],
    IsHilbertSum ℂ (fun j => W j) (fun j => (W j).subtypeₗᵢ) →
    ∀ (T : H →L[ℂ] H) (ι : Type w) (A : ι → H →L[ℂ] H) (L : J → ι → ℂ),
    IsTraceClass T → T.IsSymmetric → (∀ j x, x ∈ W j → T x ∈ W j) →
    (∀ j, ∃ C : ℕ → ℂ, ∀ i k,
      operatorTrace (summandCompression (W j) (A i * T ^ (k + 1))) = L j i * C k) →
    ∀ z : ℂ, z ≠ 0 → ∃ (D : Finset J) (c : J → ℂ), ∀ i,
      eigenspaceTrace T z (A i) = ∑ j ∈ D, c j * L j i

theorem finiteSmoothingTraceExpansion : FiniteSmoothingTraceExpansionStatement.{u, v, w} := by
  intro H _ _ _ J W _ hW T ι A L hT hSymm hInv hTrace z hz
  classical
  obtain ⟨D, hD⟩ := smoothingEigenspaceHilbertSum H J W hW T hT hSymm hInv z hz
  have hFactor (j : J) : ∃ c : ℂ, ∀ i,
      eigenspaceTrace (summandCompression (W j) T) z (summandCompression (W j) (A i)) =
        L j i * c := by
    obtain ⟨C, hC⟩ := hTrace j
    apply smoothingMomentFactorization (W j) (summandCompression (W j) T) ι
      (fun i => summandCompression (W j) (A i)) (L j) C
      (isTraceClass_compression (W j) T hT) (summandCompression_isSymmetric (W j) T hSymm)
      (fun i k => ?_) z hz
    rw [← summandCompression_mul_pow (W j) T (A i) (hInv j)]
    exact hC i k
  choose c hc using hFactor
  refine ⟨D, c, fun i => ?_⟩
  rw [hD (A i)]
  exact Finset.sum_congr rfl (fun j _ => (hc j i).trans (mul_comm _ _))

end Langlands.TraceFormula
