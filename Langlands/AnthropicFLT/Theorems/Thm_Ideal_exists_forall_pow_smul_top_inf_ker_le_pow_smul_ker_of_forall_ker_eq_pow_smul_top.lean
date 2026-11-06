/-
Ported from `Theorems/Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) :=
  P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.solution J G F γ hγs hγk φ hφk θ hθs hθc
