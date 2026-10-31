/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Ported by Worker 137 from Anthropic FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Theorems/Thm_Module_exists_projective_complex_quasiIso_of_flat_complex.lean.
Changes: FLT imports moved under Langlands.AnthropicFLT; P2M.Util removed;
P2M commands replaced by standard Lean commands; finite port options added.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_projective_complex_quasiIso_of_flat_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_projective_complex_quasiIso_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] C i) (_ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i),
      (∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0) ∧
      (∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y) ∧
      (∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
        x ∈ LinearMap.range (δ i)) ∧
      (∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
        ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) := by
  exact _root_.P2MW.S_Module_exists_projective_complex_quasiIso_of_flat_complex.solution R C d hdd n hbdd hfin0 hfin
