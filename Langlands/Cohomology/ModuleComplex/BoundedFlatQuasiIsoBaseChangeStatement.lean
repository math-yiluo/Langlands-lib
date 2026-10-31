/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Adapted by Worker 137: imported theorem type repackaged as a Prop-valued
statement in the Langlands namespace; proof and P2M imports removed.
Original source: Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib

set_option autoImplicit false

universe u

open TensorProduct

namespace Langlands.Cohomology.ModuleComplex

def BoundedFlatQuasiIsoBaseChangeStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Flat R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (_hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (_hKbdd : ∀ i, n < i → Subsingleton (K i)) (_hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[R] C i) (_hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (_h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (_h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (_hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (_hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A],
    (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → (φ 0).baseChange A x = 0 → x = 0) ∧
    (∀ y : A ⊗[R] C 0, (d 0).baseChange A y = 0 →
      ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ (φ 0).baseChange A x = y) ∧
    (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
      (φ (i + 1)).baseChange A x ∈ LinearMap.range ((d i).baseChange A) →
        x ∈ LinearMap.range ((δ i).baseChange A)) ∧
    (∀ (i : ℕ) (y : A ⊗[R] C (i + 1)), (d (i + 1)).baseChange A y = 0 →
      ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
        (φ (i + 1)).baseChange A x - y ∈ LinearMap.range ((d i).baseChange A))

end Langlands.Cohomology.ModuleComplex
