/-
Ported from `Theorems/Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (p : ∀ k, P k) (hp : ∀ k, π k (p (k + 1)) = p k) (hpθ : ∀ k, θ k (p k) = 0) :
    ∃! e : ∀ k, E k, (∀ k, τ k (e (k + 1)) = e k) ∧ ∀ k, u k (e k) = p k :=
  P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution I E τ hτs hτk P π C θ u huc hur hui p hp hpθ
