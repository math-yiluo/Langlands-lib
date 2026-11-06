/-
Ported from `Theorems/Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {GK : Type v} [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {GE : Type v} [AddCommGroup GE] [Module B GE] [Module.Finite B GE]
    {M : Type v} [AddCommGroup M] [Module B M]
    (ϑ : GK →ₗ[B] M) (θE : M →ₗ[B] GE) (hex : LinearMap.range ϑ = LinearMap.ker θE) (hθE : Function.Surjective θE)
    (F : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hF : ∀ k, I ^ (k + 1) • (⊤ : Submodule B (F k)) = ⊥)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (c : ℕ) (hlami : ∀ k, LinearMap.ker (lam (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule B GK))
    (E : ℕ → Type w) [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (θ θ' : ∀ k, M →ₗ[B] F k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k) (hθ'c : ∀ k, φ k ∘ₗ θ' (k + 1) = θ' k)
    (hθϑ : ∀ k, θ k ∘ₗ ϑ = lam k) (hθ'ϑ : ∀ k, θ' k ∘ₗ ϑ = lam k)
    (hθε : ∀ k, ε k ∘ₗ θ k = ε k ∘ₗ θ' k) :
    ∃ g : ℕ → (GE →ₗ[B] GK),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (GE →ₗ[B] GK))) ∧
      (∀ k, θ' k - θ k = lam k ∘ₗ g k ∘ₗ θE) :=
  P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution I ϑ θE hex hθE F φ hF lam hlamc c hlami E ε hlamr θ θ' hθc hθ'c hθϑ hθ'ϑ hθε
