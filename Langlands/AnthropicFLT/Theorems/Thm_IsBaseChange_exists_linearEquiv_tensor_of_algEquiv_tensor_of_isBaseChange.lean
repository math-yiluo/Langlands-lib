/-
Ported from `Theorems/Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
    {R₀ : Type u} [CommRing R₀] {R : Type u} [CommRing R] [Algebra R₀ R]
    {Γ₀ : Type u} [CommRing Γ₀] [Algebra R₀ Γ₀]
    {S : Type u} [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R₀ R S]
    (ψ : Γ₀ →ₐ[R₀] S) (θ : Γ₀ ⊗[R₀] R ≃ₐ[R₀] S)
    (hθ₁ : ∀ a : Γ₀, θ (a ⊗ₜ (1 : R)) = ψ a) (hθ₂ : ∀ r : R, θ ((1 : Γ₀) ⊗ₜ r) = algebraMap R S r)
    {L₀ : Type v} [AddCommGroup L₀] [Module R₀ L₀]
    {L : Type v} [AddCommGroup L] [Module R L] (eL : R ⊗[R₀] L₀ ≃ₗ[R] L)
    {N₀ : Type w} [AddCommGroup N₀] [Module R₀ N₀] [Module Γ₀ N₀] [IsScalarTower R₀ Γ₀ N₀]
    (f₀ : L₀ →ₗ[R₀] N₀) (hf₀ : IsBaseChange Γ₀ f₀)
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : L →ₗ[R] N) (hf : IsBaseChange S f) :
    ∃ Φ : R ⊗[R₀] N₀ ≃ₗ[R] N,
      (∀ x₀ : L₀, Φ ((1 : R) ⊗ₜ f₀ x₀) = f (eL ((1 : R) ⊗ₜ x₀))) ∧
      (∀ (r : R) (γ : Γ₀) (n₀ : N₀), Φ (r ⊗ₜ (γ • n₀)) = r • (ψ γ • Φ ((1 : R) ⊗ₜ n₀))) ∧
      (∀ (N' : Type w) [AddCommGroup N'] [Module R N'] (g g' : R ⊗[R₀] N₀ →ₗ[R] N'),
          (∀ (r : R) (γ : Γ₀) (x₀ : L₀), g (r ⊗ₜ (γ • f₀ x₀)) = g' (r ⊗ₜ (γ • f₀ x₀))) → g = g') :=
  P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution ψ θ hθ₁ hθ₂ eL f₀ hf₀ f hf
