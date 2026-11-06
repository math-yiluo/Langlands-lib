/-
Ported from `Theorems/Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type u} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE) (hp : Function.Surjective p)
    (F E : ℕ → Type u) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))

    (ℓ : ∀ n, (Fin r → B) →ₗ[B] F n) (hℓε : ∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) (hℓφ : ∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n)
    (δs : ∀ n, ↥(LinearMap.ker p) →ₗ[B] GK) (hδs : ∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype)
    (hδsc : ∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))

    (δ : ↥(LinearMap.ker p) →ₗ[B] GK)
    (hδ : ∀ n, δ - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)) ⊔
      LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker p).subtype)) :
    ∃ ℓ' : ∀ k, (Fin r → B) →ₗ[B] F k,
      (∀ k, φ k ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ε k ∘ₗ ℓ' k = ψE k ∘ₗ p) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker p).subtype = lam k ∘ₗ δ) :=
  P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution J p hp F E φ hφs hφk ε ψE lam hlamc hlamr ℓ hℓε hℓφ δs hδs hδsc δ hδ
