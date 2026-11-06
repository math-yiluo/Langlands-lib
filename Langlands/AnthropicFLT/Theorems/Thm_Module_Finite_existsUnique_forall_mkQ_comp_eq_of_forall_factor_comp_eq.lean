/-
Ported from `Theorems/Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (ψ : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • (⊤ : Submodule A N)))
    (hψ : ∀ n : ℕ,
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ∘ₗ ψ (n + 1) = ψ n) :
    ∃! Φ : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : M →ₗ[A] N), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N))) ∘ₗ g = ψ n) :=
  P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.solution I ψ hψ
