/-
Ported from `Theorems/Thm_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
    {B : Type u} [CommRing B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) :
    ∃ Φ : ((↥(LinearMap.ker p₂) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₂).subtype)) ≃ₗ[B]
        ((↥(LinearMap.ker p₁) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₁).subtype)),
      ∀ (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)), p₂ ∘ₗ g = p₁ →
        ∀ (g' : ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂)),
          (∀ s : ↥(LinearMap.ker p₁), ((g' s : ↥(LinearMap.ker p₂)) : Fin r₂ → B) = g (s : Fin r₁ → B)) →
          ∀ δ : ↥(LinearMap.ker p₂) →ₗ[B] N,
            Φ (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ g') :=
  P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.solution p₁ p₂ hp₁ hp₂
