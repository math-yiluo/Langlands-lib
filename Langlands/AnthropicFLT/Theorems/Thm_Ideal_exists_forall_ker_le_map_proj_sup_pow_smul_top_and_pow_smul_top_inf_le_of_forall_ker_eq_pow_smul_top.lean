/-
Ported from `Theorems/Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (F P : ℕ → Type v)
    [∀ n, AddCommGroup (F n)] [∀ n, Module B (F n)] [∀ n, Module.Finite B (F n)]
    [∀ n, AddCommGroup (P n)] [∀ n, Module B (P n)] [∀ n, Module.Finite B (P n)]
    (φ : ∀ n, F (n + 1) →ₗ[B] F n) (hφs : ∀ n, Function.Surjective (φ n))
    (hφk : ∀ n, LinearMap.ker (φ n) = J ^ (n + 1) • (⊤ : Submodule B (F (n + 1))))
    (π : ∀ n, P (n + 1) →ₗ[B] P n) (hπs : ∀ n, Function.Surjective (π n))
    (hπk : ∀ n, LinearMap.ker (π n) = J ^ (n + 1) • (⊤ : Submodule B (P (n + 1))))
    (u : ∀ n, F n →ₗ[B] P n) (hu : ∀ n, π n ∘ₗ u (n + 1) = u n ∘ₗ φ n)
    (K : Submodule B (∀ n, F n))
    (hK : ∀ x : ∀ n, F n, x ∈ K ↔ (∀ n, φ n (x (n + 1)) = x n) ∧ ∀ n, u n (x n) = 0) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      LinearMap.ker (u n) ≤ K.map (LinearMap.proj n) ⊔ J ^ (k + 1) • (⊤ : Submodule B (F n)) ∧
      J ^ n • (⊤ : Submodule B (F n)) ⊓ K.map (LinearMap.proj n) ≤ J ^ k • K.map (LinearMap.proj n) :=
  P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution J F P φ hφs hφk π hπs hπk u hu K hK
