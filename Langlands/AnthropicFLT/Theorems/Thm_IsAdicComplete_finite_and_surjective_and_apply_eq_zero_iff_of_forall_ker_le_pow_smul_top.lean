/-
Ported from `Theorems/Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) :=
  P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution I M t hI ht hker L hL
