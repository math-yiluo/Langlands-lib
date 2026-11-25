/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Block matrices of constant rank

A block matrix `[[B, C], [D, E]]` whose block `B` is invertible and whose Schur complement
`E - D B⁻¹ C` vanishes is equivalent to `[[1, 0], [0, 0]]`
(`Matrix.exists_eq_mul_fromBlocks_one_zero`). The Schur complement vanishes as soon as the
specializations of the matrix along a jointly injective family of ring maps to fields have rank at
most the size of `B` (`Matrix.schur_eq_zero_of_rank_le`): its entries are, up to the unit
`det B`, the `(|B| + 1)`-minors bordering `B`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R] {r κ' ι' : Type*} [Fintype r] [DecidableEq r] [Fintype κ']
  [Fintype ι'] [DecidableEq κ'] [DecidableEq ι']

/-- A block matrix whose upper left block is invertible and whose Schur complement vanishes is
equivalent to the block matrix `[[1, 0], [0, 0]]`. -/
lemma exists_eq_mul_fromBlocks_one_zero (B : Matrix r r R) (C : Matrix r ι' R) (D : Matrix κ' r R)
    (E : Matrix κ' ι' R) (hB : IsUnit B.det) (hS : E - D * B⁻¹ * C = 0) :
    ∃ (P : Matrix (r ⊕ κ') (r ⊕ κ') R) (Q : Matrix (r ⊕ ι') (r ⊕ ι') R),
      IsUnit P.det ∧ IsUnit Q.det ∧
        fromBlocks B C D E = P * (fromBlocks 1 0 0 0 : Matrix (r ⊕ κ') (r ⊕ ι') R) * Q := by
  let := invertibleOfIsUnitDet B hB
  refine ⟨fromBlocks 1 0 (D * ⅟B) 1 * fromBlocks B 0 0 1, fromBlocks 1 (⅟B * C) 0 1, ?_, ?_, ?_⟩
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
    simpa using hB
  · rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]
    exact isUnit_one
  · rw [fromBlocks_eq_of_invertible₁₁ B C D E, invOf_eq_nonsing_inv, hS,
      Matrix.mul_assoc _ (fromBlocks B 0 0 1),
      fromBlocks_multiply]
    simp only [fromBlocks_multiply]
    simp [Matrix.mul_assoc]

end Matrix

namespace Matrix

variable {R K T : Type*} [CommRing R] [Field K] {r κ' ι' : Type*} [Fintype r] [DecidableEq r]
  [Fintype ι']

/-- If the specializations of a block matrix along a jointly injective family of ring maps to
fields all have rank at most the size of an invertible upper left block, the Schur complement of
that block vanishes. -/
lemma schur_eq_zero_of_rank_le (f : T → R →+* K) (hf : ∀ x, (∀ t, f t x = 0) → x = 0)
    (B : Matrix r r R) (C : Matrix r ι' R) (D : Matrix κ' r R) (E : Matrix κ' ι' R)
    [Invertible B] (hr : ∀ t, ((fromBlocks B C D E).map (f t)).rank ≤ Fintype.card r) :
    E - D * ⅟B * C = 0 := by
  ext i j
  refine hf _ fun t ↦ ?_
  let N : Matrix (r ⊕ Unit) (r ⊕ Unit) K :=
    ((fromBlocks B C D E).map (f t)).submatrix (Sum.elim Sum.inl fun _ ↦ Sum.inr i)
      (Sum.elim Sum.inl fun _ ↦ Sum.inr j)
  have hN : N.det = 0 := by
    by_contra h
    have := (rank_of_det_ne_zero h).symm.trans_le
      ((rank_submatrix_le _ _ _).trans (hr t))
    simp at this
  let iB : Invertible (B.map (f t)) :=
    ⟨(⅟B).map (f t), by rw [← Matrix.map_mul, invOf_mul_self, Matrix.map_one _ (map_zero _)
      (map_one _)], by rw [← Matrix.map_mul, mul_invOf_self, Matrix.map_one _ (map_zero _)
      (map_one _)]⟩
  have hN' : N = fromBlocks (B.map (f t)) (C.map (f t) |>.submatrix id fun _ : Unit ↦ j)
      (D.map (f t) |>.submatrix (fun _ : Unit ↦ i) id) (fun _ _ ↦ f t (E i j)) := by
    ext (a | a) (b | b) <;> rfl
  rw [hN', det_fromBlocks₁₁, Matrix.det_unique (n := Unit)] at hN
  have hdet : (B.map (f t)).det ≠ 0 := (isUnit_det_of_invertible _).ne_zero
  have h2 := (mul_eq_zero.1 hN).resolve_left hdet
  refine Eq.trans ?_ h2
  simp only [sub_apply, map_sub, Matrix.mul_apply, map_sum, map_mul, Matrix.submatrix_apply,
    Matrix.map_apply, id]
  rfl

end Matrix
