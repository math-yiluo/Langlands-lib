/-
Ported from `Theorems/Thm_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor open MvPolynomial hiding exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
attribute [local instance] MvPolynomial.gradedAlgebra

theorem MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
    (n : ℕ) (K : Type uz) [Field K] [Infinite K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (hsat : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) → F ∈ I) :
    ∃ a : Fin (n + 1) → K, ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∑ i : Fin (n + 1), MvPolynomial.C (a i) * MvPolynomial.X i) * F ∈ I → F ∈ I :=
  P2MW.S_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem.solution n K I hI hsat
