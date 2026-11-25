/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exactness of a complex of free modules from invertible minors

Let `R^{ι₀} --A--> R^{ι₁} --B--> R^{ι₂}` be a complex of finite free modules over a commutative
ring, `B * A = 0`. If `A` has an invertible `a × a` minor and `B` has an invertible `b × b` minor
with `a + b = |ι₁|`, then the complex is exact at `R^{ι₁}`. This is the local algebra behind the
statement that the cohomology of a complex of finite free modules vanishes near a point where its
fibre cohomology vanishes.

## Main statements

- `Matrix.exists_mulVec_eq_of_isUnit_det_submatrix`
-/

@[expose] public section

open Matrix

variable {R : Type*} [CommRing R] {ι₀ ι₁ ι₂ α β : Type*} [Fintype ι₀] [Fintype ι₁]
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **A complex of free modules with invertible minors of complementary sizes is exact.** Let
`B * A = 0` for matrices `A : R^{ι₀} → R^{ι₁}` and `B : R^{ι₁} → R^{ι₂}`. If an `a × a` minor of
`A` and a `b × b` minor of `B` are units, with `a + b = |ι₁|`, then every `v` with `B v = 0` is of
the form `A w`.

The columns of `A` through the first minor and a right inverse `S` of the rows of `B` through the
second minor form a square matrix `Φ = (A' | S)`, which is invertible since `(L ; B') Φ` is block
unitriangular for a left inverse `L` of `A'`. Writing `v = A' w₁ + S w₂` and applying `B'` gives
`w₂ = 0`. -/
theorem Matrix.exists_mulVec_eq_of_isUnit_det_submatrix (A : Matrix ι₁ ι₀ R)
    (B : Matrix ι₂ ι₁ R) (hBA : B * A = 0) (e₁ : α → ι₁) (e₀ : α → ι₀)
    (hA : IsUnit (A.submatrix e₁ e₀).det) (f₂ : β → ι₂) (f₁ : β → ι₁)
    (hB : IsUnit (B.submatrix f₂ f₁).det)
    (hcard : Fintype.card α + Fintype.card β = Fintype.card ι₁) {v : ι₁ → R}
    (hv : B *ᵥ v = 0) : ∃ w : ι₀ → R, A *ᵥ w = v := by
  classical
  set A' : Matrix ι₁ α R := A.submatrix id e₀
  set B' : Matrix β ι₁ R := B.submatrix f₂ id
  set L : Matrix α ι₁ R := (A.submatrix e₁ e₀)⁻¹ * (1 : Matrix ι₁ ι₁ R).submatrix e₁ id
  set S : Matrix ι₁ β R := (1 : Matrix ι₁ ι₁ R).submatrix id f₁ * (B.submatrix f₂ f₁)⁻¹
  have hLA : L * A' = 1 := by
    have : (1 : Matrix ι₁ ι₁ R).submatrix e₁ id * A' = A.submatrix e₁ e₀ := by
      ext a b; simp [A', Matrix.mul_apply, Matrix.one_apply]
    rw [Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hA]
  have hBS : B' * S = 1 := by
    have : B' * (1 : Matrix ι₁ ι₁ R).submatrix id f₁ = B.submatrix f₂ f₁ := by
      ext a b; simp [B', Matrix.mul_apply, Matrix.one_apply]
    rw [← Matrix.mul_assoc, this, Matrix.mul_nonsing_inv _ hB]
  have hBA' : B' * A' = 0 := by
    have : B' * A' = (B * A).submatrix f₂ e₀ := by
      ext a b; simp [A', B', Matrix.mul_apply]
    rw [this, hBA]; rfl
  have hB'v : B' *ᵥ v = 0 := by
    ext b; have := congrFun hv (f₂ b); simpa [B', Matrix.mulVec, dotProduct] using this
  -- the square matrix `Φ = (A' | S)` is invertible
  set Φ : Matrix ι₁ (α ⊕ β) R := Matrix.fromCols A' S
  set Ψ : Matrix (α ⊕ β) ι₁ R := Matrix.fromRows L B'
  have hΨΦ : Ψ * Φ = Matrix.fromBlocks 1 (L * S) 0 1 := by
    rw [Matrix.fromRows_mul_fromCols, hLA, hBA', hBS]
  obtain ⟨e⟩ : Nonempty (α ⊕ β ≃ ι₁) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_sum, hcard])⟩
  set Φ' : Matrix ι₁ ι₁ R := Φ.submatrix id e.symm
  set Ψ' : Matrix ι₁ ι₁ R := Ψ.submatrix e.symm id
  have hdet : IsUnit (Ψ' * Φ').det := by
    have : Ψ' * Φ' = (Ψ * Φ).submatrix e.symm e.symm := by
      ext a b
      simp [Ψ', Φ', Matrix.mul_apply]
    rw [this, Matrix.det_submatrix_equiv_self, hΨΦ, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hΦ' : IsUnit Φ'.det := by
    rw [Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  set u : ι₁ → R := Φ'⁻¹ *ᵥ v
  have hv' : v = Φ *ᵥ (u ∘ e) := by
    have h1 : Φ' *ᵥ u = v := by
      simp only [u, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΦ', Matrix.one_mulVec]
    rw [← h1]
    ext i
    simp only [Φ', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ by simp)
  have hdecomp : Φ *ᵥ (u ∘ e) = A' *ᵥ (fun a ↦ u (e (Sum.inl a))) +
      S *ᵥ (fun b ↦ u (e (Sum.inr b))) := by
    ext i
    simp [Φ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromCols]
  have hw₂ : (fun b ↦ u (e (Sum.inr b))) = 0 := by
    have := congrArg (B' *ᵥ ·) (hv'.trans hdecomp)
    simp only [hB'v, Matrix.mulVec_add, Matrix.mulVec_mulVec, hBA', hBS, Matrix.zero_mulVec,
      Matrix.one_mulVec, zero_add] at this
    exact this.symm
  refine ⟨(1 : Matrix ι₀ ι₀ R).submatrix id e₀ *ᵥ (fun a ↦ u (e (Sum.inl a))), ?_⟩
  rw [Matrix.mulVec_mulVec, hv', hdecomp, hw₂, Matrix.mulVec_zero, add_zero]
  congr 1
  ext i a
  simp [A', Matrix.mul_apply, Matrix.one_apply]
