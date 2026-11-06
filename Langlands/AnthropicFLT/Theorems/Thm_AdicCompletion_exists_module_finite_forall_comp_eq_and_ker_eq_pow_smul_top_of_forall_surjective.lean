/-
Ported from `Theorems/Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[B] M n)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) = I ^ (n + 1) • (⊤ : Submodule B (M (n + 1))))
    (hfin : Module.Finite B (M 0)) :
    ∃ (L : Type v) (_ : AddCommGroup L) (_ : Module B L) (_ : Module (AdicCompletion I B) L)
      (_ : IsScalarTower B (AdicCompletion I B) L) (_ : Module.Finite (AdicCompletion I B) L)
      (pr : ∀ n : ℕ, L →ₗ[B] M n),
      (∀ (n : ℕ) (x : L), t n (pr (n + 1) x) = pr n x) ∧
      (∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0) ∧
      (∀ m : ∀ n : ℕ, M n, (∀ n : ℕ, t n (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n) ∧
      (∀ n : ℕ, Function.Surjective (pr n)) ∧
      (∀ n : ℕ, LinearMap.ker (pr n) = I ^ (n + 1) • (⊤ : Submodule B L)) :=
  P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution I hI M t ht hker hfin
