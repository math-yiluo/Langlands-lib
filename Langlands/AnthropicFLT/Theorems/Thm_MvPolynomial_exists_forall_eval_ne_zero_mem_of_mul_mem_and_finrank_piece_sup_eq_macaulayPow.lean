/-
Ported from `Theorems/Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open _root_.AlgebraicGeometry.HilbertFunctor open _root_.MvPolynomial hiding finrank_piece_succ_le_macaulayPow exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le

theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
    (n m : ℕ) (K : Type uz) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      (∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → (∑ i, C (a i) * X i) * f ∈ J → f ∈ J) ∧
      Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) ∧
      Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) +
          Module.finrank K (piece J m) = Nat.macaulayPow m (Module.finrank K (piece J m)) :=
  P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.solution n m K J hJ hmax
