/-
Ported from `Theorems/Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (J : ℕ → Submodule B N) (hJ : ∀ k, J (k + 1) ≤ J k)
    (hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B N) ≤ J k)
    (c : ℕ) (hJI : ∀ k, J (k + c) ≤ I ^ (k + 1) • (⊤ : Submodule B N))
    (f : ∀ k, M →ₗ[B] N ⧸ J k)
    (hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k) :
    ∃ g : ℕ → (M →ₗ[B] N),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (M →ₗ[B] N))) ∧
      (∀ k, (J k).mkQ ∘ₗ g k = f k) :=
  P2MW.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible.solution I J hJ hIJ c hJI f hf
