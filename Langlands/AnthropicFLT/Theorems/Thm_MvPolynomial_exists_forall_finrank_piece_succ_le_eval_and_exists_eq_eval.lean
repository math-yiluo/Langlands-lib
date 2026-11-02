/-
Ported from `Theorems/Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type uz) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ e : ℕ, D₀ ≤ e →
      (∀ (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) →
        (Module.finrank K (piece J (e + 1)) : ℚ) ≤ P.eval ((e : ℚ) + 1)) ∧
      ∃ (K : Type uz) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) ∧
        (Module.finrank K (piece J (e + 1)) : ℚ) = P.eval ((e : ℚ) + 1) :=
  P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.solution n P hP
