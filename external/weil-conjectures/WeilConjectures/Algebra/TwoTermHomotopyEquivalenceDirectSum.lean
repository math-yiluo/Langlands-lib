/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module

/-! # Direct sums of the terms of homotopy equivalent two-term complexes

Source: Stacks Project, Algebra, Lemma 00S3 (lemma-sum-two-terms)
(blueprint: lem-weil-pbc-two-term-homotopy-equivalence-direct-sum).
-/

@[expose] public section

universe u v₁ v₀ w₁ w₀

namespace Module

/-- Homotopy equivalent two-term complexes have isomorphic crosswise binary direct sums.
The binary direct sum of modules is represented by the product with componentwise operations;
this is the finite two-summand case of `DirectSum` (def-weil-pbc-direct-sum-modules).

Source: Stacks Project, Algebra, Lemma 00S3 (lemma-sum-two-terms)
(blueprint: lem-weil-pbc-two-term-homotopy-equivalence-direct-sum).

Proof plan:
1. Set `P = A₁ × B₀` and `Q = B₁ × A₀`, the binary direct sums from
   def-weil-pbc-direct-sum-modules. Define linear maps
   `C(a,b) = (φ₁(a) - h'(b), dA(a) + ψ₀(b))` and
   `D(c,e) = (ψ₁(c) + h(e), -dB(c) + φ₀(e))`.
2. Expand both compositions using the two chain-map equations and the four homotopy equations.
   The first component of `DC(a,b)` is `a + (h ∘ ψ₀ - ψ₁ ∘ h')(b)` and its second is `b`.
   The first component of `CD(c,e)` is `c + (φ₁ ∘ h - h' ∘ φ₀)(e)` and its second is `e`.
   Thus `DC = U_P` and `CD = U_Q` are upper triangular maps with identity diagonal.
3. Subtracting the off-diagonal term gives inverses for both triangular maps.
   Then `L = U_P⁻¹ ∘ D` is a left inverse for `C`, while `T = D ∘ U_Q⁻¹` is a right inverse.
   The equality `L = L ∘ (C ∘ T) = (L ∘ C) ∘ T = T` gives a common inverse.
   Hence `C` yields the required linear equivalence between the two direct sums.
-/
theorem prod_linearEquiv_of_twoTermHomotopy
    (R : Type u) [CommRing R]
    (A₁ : Type v₁) (A₀ : Type v₀) (B₁ : Type w₁) (B₀ : Type w₀)
    [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁] [AddCommGroup B₀]
    [Module R A₁] [Module R A₀] [Module R B₁] [Module R B₀]
    (dA : A₁ →ₗ[R] A₀) (dB : B₁ →ₗ[R] B₀)
    (φ₁ : A₁ →ₗ[R] B₁) (φ₀ : A₀ →ₗ[R] B₀)
    (ψ₁ : B₁ →ₗ[R] A₁) (ψ₀ : B₀ →ₗ[R] A₀)
    (hφ : dB.comp φ₁ = φ₀.comp dA)
    (hψ : dA.comp ψ₁ = ψ₀.comp dB)
    (h : A₀ →ₗ[R] A₁) (h' : B₀ →ₗ[R] B₁)
    (hA₁ : LinearMap.id - ψ₁.comp φ₁ = h.comp dA)
    (hA₀ : LinearMap.id - ψ₀.comp φ₀ = dA.comp h)
    (hB₁ : LinearMap.id - φ₁.comp ψ₁ = h'.comp dB)
    (hB₀ : LinearMap.id - φ₀.comp ψ₀ = dB.comp h') :
    Nonempty ((A₁ × B₀) ≃ₗ[R] (B₁ × A₀)) := by
  have hA₁' (a : A₁) : a - ψ₁ (φ₁ a) = h (dA a) := LinearMap.congr_fun hA₁ a
  have hA₀' (e : A₀) : e - ψ₀ (φ₀ e) = dA (h e) := LinearMap.congr_fun hA₀ e
  have hB₁' (c : B₁) : c - φ₁ (ψ₁ c) = h' (dB c) := LinearMap.congr_fun hB₁ c
  have hB₀' (b : B₀) : b - φ₀ (ψ₀ b) = dB (h' b) := LinearMap.congr_fun hB₀ b
  have hφ' (a : A₁) : dB (φ₁ a) = φ₀ (dA a) := LinearMap.congr_fun hφ a
  have hψ' (c : B₁) : dA (ψ₁ c) = ψ₀ (dB c) := LinearMap.congr_fun hψ c
  -- The crosswise map `(a, b) ↦ (φ₁ a - h' b, dA a + ψ₀ b)`.
  let C : (A₁ × B₀) →ₗ[R] (B₁ × A₀) :=
    (φ₁ ∘ₗ LinearMap.fst R A₁ B₀ - h' ∘ₗ LinearMap.snd R A₁ B₀).prod
      (dA ∘ₗ LinearMap.fst R A₁ B₀ + ψ₀ ∘ₗ LinearMap.snd R A₁ B₀)
  refine ⟨LinearEquiv.ofBijective C ⟨(injective_iff_map_eq_zero C).2 ?_, ?_⟩⟩
  · rintro ⟨a, b⟩ hab
    have h₁ : φ₁ a = h' b := sub_eq_zero.1 (congr_arg Prod.fst hab)
    have h₂ : dA a + ψ₀ b = 0 := congr_arg Prod.snd hab
    obtain rfl : b = 0 := by
      rw [← sub_add_cancel b (φ₀ (ψ₀ b)), hB₀' b, ← h₁, hφ', ← map_add, h₂, map_zero]
    rw [map_zero, add_zero] at h₂
    rw [map_zero] at h₁
    rw [← sub_add_cancel a (ψ₁ (φ₁ a)), hA₁' a, h₁, h₂, map_zero, map_zero, add_zero,
      Prod.mk_zero_zero]
  · rintro ⟨c, e⟩
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + (φ₁ (h e) - h' (φ₀ e)) := ⟨_, (sub_add_cancel _ _).symm⟩
    refine ⟨(ψ₁ c + h e, -dB c + φ₀ e), Prod.ext ?_ ?_⟩
    · simp only [C, LinearMap.prod_apply, Function.prod, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, map_add, map_neg]
      rw [← sub_eq_zero, ← hB₁' c]
      abel
    · simp only [C, LinearMap.prod_apply, Function.prod, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, map_add, map_neg, hψ']
      rw [← sub_eq_zero, ← hA₀' e]
      abel

end Module
