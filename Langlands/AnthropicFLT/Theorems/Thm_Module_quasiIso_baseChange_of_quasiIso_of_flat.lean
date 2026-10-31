/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Ported by Worker 137 from Anthropic FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Theorems/Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean.
Changes: FLT imports moved under Langlands.AnthropicFLT; P2M.Util removed;
P2M commands replaced by standard Lean commands; finite port options added.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_quasiIso_baseChange_of_quasiIso_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem Module.quasiIso_baseChange_of_quasiIso_of_flat
    (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Flat R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hKbdd : ∀ i, n < i → Subsingleton (K i)) (hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[R] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → (φ 0).baseChange A x = 0 → x = 0) ∧
    (∀ y : A ⊗[R] C 0, (d 0).baseChange A y = 0 →
      ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ (φ 0).baseChange A x = y) ∧
    (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
      (φ (i + 1)).baseChange A x ∈ LinearMap.range ((d i).baseChange A) →
        x ∈ LinearMap.range ((δ i).baseChange A)) ∧
    (∀ (i : ℕ) (y : A ⊗[R] C (i + 1)), (d (i + 1)).baseChange A y = 0 →
      ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
        (φ (i + 1)).baseChange A x - y ∈ LinearMap.range ((d i).baseChange A)) := by
  exact _root_.P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat.solution R K δ hδδ C d hdd n hKbdd hCbdd φ hφ h0inj h0surj hinj hsurj A
