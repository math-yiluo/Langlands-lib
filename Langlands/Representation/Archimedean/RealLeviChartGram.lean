import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Langlands.LinearAlgebra.TriangularUnitary
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real

/-!
# Trailing principal minors and the Gram determinants of a block lower triangular matrix

Algebraic identities for the proof of `RealLeviChartIntegrableStatement`.

* `tm r S` is the principal minor of `S` on the rows and columns `≥ r`, so that the Gram
  determinant `GramFormula.gram r x` is `tm r (x xᵀ)` (`gram_eq_tm`).
* For an upper triangular `T`, `tm r (T S Tᵀ) = (∏_{p ≥ r} T_pp)² · tm r S` (`tm_conj`), and
  `tm r (1 + y yᵀ) = 1 + ∑_{p ≥ r} y_p²` (`tm_one_add_vecMulVec`).
* For a family of columns `V_0, …, V_{a-1} ∈ ℝ^M`, `colGram j V = ∑_{k < j} V_k V_kᵀ`.
* `blockLower V B` is the matrix `[[1, 0], [W, B]]` of size `a + M`, where the columns of `W`
  are the `V_k`. Its Gram determinants are `det (colGram l V + B Bᵀ)` for `l ≤ a`
  (`gram_blockLower_of_le`) and `tm r (colGram a V + B Bᵀ)` at the position `a + r`
  (`gram_blockLower_add`).
-/

noncomputable section

open Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

namespace RealLeviChartGram

open GramFormula

/-! ## Trailing principal minors -/

section Minor

variable {n : ℕ}

/-- `S` on the rows and columns `≥ r`, padded by the identity matrix. -/
def padS (r : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if r ≤ (p : ℕ) ∧ r ≤ (q : ℕ) then S p q else (1 : Matrix (Fin n) (Fin n) ℝ) p q

/-- The principal minor of `S` on the rows and columns `≥ r`. -/
def tm (r : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : ℝ := (padS r S).det

theorem gram_eq_tm (r : ℕ) (x : Matrix (Fin n) (Fin n) ℝ) : gram r x = tm r (x * xᵀ) := rfl

theorem padS_zero (S : Matrix (Fin n) (Fin n) ℝ) : padS 0 S = S := by
  ext p q
  simp [padS]

theorem tm_zero (S : Matrix (Fin n) (Fin n) ℝ) : tm 0 S = S.det := by
  rw [tm, padS_zero]

theorem padS_one (r : ℕ) : padS r (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext p q
  simp [padS]

theorem tm_one (r : ℕ) : tm r (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [tm, padS_one, det_one]

theorem mul_mul_transpose_apply (A Y B : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (A * Y * Bᵀ) p q = ∑ j, ∑ k, A p j * Y j k * B q k := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem padS_conj {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsUpperTriangular) (r : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    padS r (T * X * Tᵀ) = padded r T * padS r X * (padded r T)ᵀ := by
  ext p q
  rw [mul_mul_transpose_apply]
  by_cases hp : r ≤ (p : ℕ)
  · by_cases hq : r ≤ (q : ℕ)
    · rw [padS, of_apply, ite_eq_left ⟨hp, hq⟩, mul_mul_transpose_apply]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [padded_apply_of_le hT hp, padded_apply_of_le hT hq]
      by_cases hj : r ≤ (j : ℕ)
      · by_cases hk : r ≤ (k : ℕ)
        · rw [padS, of_apply, ite_eq_left ⟨hj, hk⟩]
        · have h0 : T q k = 0 := hT (show k < q by rw [Fin.lt_def]; omega)
          rw [h0, mul_zero, mul_zero]
      · have h0 : T p j = 0 := hT (show j < p by rw [Fin.lt_def]; omega)
        rw [h0, zero_mul, zero_mul, zero_mul, zero_mul]
    · have hq' : (q : ℕ) < r := by omega
      have hpq : p ≠ q := fun h => by rw [h] at hp; omega
      rw [padS, of_apply, ite_eq_right (fun h => hq h.2), Matrix.one_apply_ne hpq]
      have h1 : ∀ j, ∑ k, padded r T p j * padS r X j k * padded r T q k =
          padded r T p j * padS r X j q := by
        intro j
        simp only [padded_apply_of_lt T hq', Matrix.one_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp only [h1]
      have h2 : ∀ j, padded r T p j * padS r X j q = if j = q then T p q else 0 := by
        intro j
        rw [padS, of_apply, ite_eq_right (fun h => hq h.2), padded_apply_of_le hT hp,
          Matrix.one_apply]
        split_ifs with h
        · rw [h, mul_one]
        · rw [mul_zero]
      simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact (hT (show q < p by rw [Fin.lt_def]; omega)).symm
  · have hp' : (p : ℕ) < r := by omega
    rw [padS, of_apply, ite_eq_right (fun h => hp h.1)]
    have h1 : ∀ j, (∑ k, padded r T p j * padS r X j k * padded r T q k) =
        if p = j then ∑ k, padS r X p k * padded r T q k else 0 := by
      intro j
      rw [padded_apply_of_lt T hp', Matrix.one_apply]
      split_ifs with h
      · rw [h]
        simp only [one_mul]
      · simp only [zero_mul, Finset.sum_const_zero]
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h2 : ∀ k, padS r X p k * padded r T q k = if p = k then padded r T q p else 0 := by
      intro k
      rw [padS, of_apply, ite_eq_right (fun h => hp h.1), Matrix.one_apply]
      split_ifs with h
      · rw [h, one_mul]
      · rw [zero_mul]
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hq : r ≤ (q : ℕ)
    · have hpq : p ≠ q := fun h => by rw [h] at hp'; omega
      rw [padded_apply_of_le hT hq, Matrix.one_apply_ne hpq]
      exact (hT (show p < q by rw [Fin.lt_def]; omega)).symm
    · rw [padded_apply_of_lt T (by omega), Matrix.one_apply, Matrix.one_apply]
      by_cases h : p = q
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- `tm r (T S Tᵀ) = (∏_{p ≥ r} T_pp)² · tm r S` for an upper triangular `T`. -/
theorem tm_conj {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsUpperTriangular) (r : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    tm r (T * X * Tᵀ) = diagonalTail r T ^ 2 * tm r X := by
  rw [tm, tm, padS_conj hT, det_mul, det_mul, det_transpose, det_padded hT]
  ring

theorem tm_one_add_vecMulVec (r : ℕ) (y : Fin n → ℝ) :
    tm r (1 + vecMulVec y y) = 1 + ∑ p : Fin n, if r ≤ (p : ℕ) then y p ^ 2 else 0 := by
  set z : Fin n → ℝ := fun p => if r ≤ (p : ℕ) then y p else 0 with hz
  have h : padS r (1 + vecMulVec y y) = 1 + vecMulVec z z := by
    ext p q
    simp only [padS, of_apply, Matrix.add_apply, vecMulVec_apply, hz]
    by_cases hp : r ≤ (p : ℕ)
    · by_cases hq : r ≤ (q : ℕ)
      · rw [ite_eq_left ⟨hp, hq⟩, ite_eq_left hp, ite_eq_left hq]
      · rw [ite_eq_right (fun h => hq h.2), ite_eq_right hq, mul_zero, add_zero]
    · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp, zero_mul, add_zero]
  rw [tm, h, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hz]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

/-- `padS r (1 + G) = 1 + D G D` with `D = diag(1_{p ≥ r})`. -/
theorem padS_one_add (r : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) :
    padS r (1 + G) =
      1 + diagonal (fun p : Fin n => if r ≤ (p : ℕ) then (1 : ℝ) else 0) * G *
        diagonal (fun p : Fin n => if r ≤ (p : ℕ) then (1 : ℝ) else 0) := by
  ext p q
  simp only [padS, of_apply, Matrix.add_apply, diagonal_mul, mul_diagonal]
  by_cases hp : r ≤ (p : ℕ)
  · by_cases hq : r ≤ (q : ℕ)
    · rw [ite_eq_left ⟨hp, hq⟩, ite_eq_left hp, ite_eq_left hq, one_mul, mul_one]
    · rw [ite_eq_right (fun h => hq h.2), ite_eq_right hq, mul_zero, add_zero]
  · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp, zero_mul, zero_mul, add_zero]

theorem tm_pos {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) (r : ℕ) :
    0 < tm r (1 + G) := by
  rw [tm, padS_one_add]
  set D := diagonal (fun p : Fin n => if r ≤ (p : ℕ) then (1 : ℝ) else 0)
  have hD : Dᴴ = D := by
    rw [diagonal_conjTranspose]
    congr 1
  have hDG : (D * G * D).PosSemidef := by
    have := hG.mul_mul_conjTranspose_same D
    rwa [hD] at this
  exact (PosDef.one.add_posSemidef hDG).det_pos

theorem det_one_add_pos {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) :
    0 < (1 + G).det := by
  rw [← tm_zero]
  exact tm_pos hG 0

end Minor

/-! ## Gram matrices of column families -/

section Columns

variable {a M : ℕ}

/-- `∑_{k < j} V_k V_kᵀ` for a family of columns `V_0, …, V_{a-1} ∈ ℝ^M`. -/
def colGram (j : ℕ) (V : Fin a → Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  ∑ k : Fin a, if (k : ℕ) < j then vecMulVec (V k) (V k) else 0

theorem posSemidef_colGram (j : ℕ) (V : Fin a → Fin M → ℝ) : (colGram j V).PosSemidef := by
  refine posSemidef_sum _ fun k _ => ?_
  split_ifs
  · have := posSemidef_vecMulVec_self_star (V k)
    rwa [star_trivial] at this
  · exact PosSemidef.zero

theorem colGram_mulVec (T : Matrix (Fin M) (Fin M) ℝ) (j : ℕ) (V : Fin a → Fin M → ℝ) :
    colGram j (fun k => T *ᵥ V k) = T * colGram j V * Tᵀ := by
  simp only [colGram, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
  · rw [Matrix.mul_zero, Matrix.zero_mul]

theorem colGram_snoc_of_le {a' : ℕ} (V' : Fin a' → Fin M → ℝ) (u : Fin M → ℝ) {j : ℕ}
    (hj : j ≤ a') : colGram j (Fin.snoc V' u : Fin (a' + 1) → Fin M → ℝ) = colGram j V' := by
  rw [colGram, Fin.sum_univ_castSucc, colGram]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [ite_eq_right (by omega), add_zero]

theorem colGram_snoc_succ {a' : ℕ} (V' : Fin a' → Fin M → ℝ) (u : Fin M → ℝ) :
    colGram (a' + 1) (Fin.snoc V' u : Fin (a' + 1) → Fin M → ℝ) =
      colGram a' V' + vecMulVec u u := by
  rw [colGram, Fin.sum_univ_castSucc, colGram]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [ite_eq_left (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ite_eq_left (by omega), ite_eq_left k.2]

end Columns

/-! ## The block matrix `[[1, 0], [W, B]]` -/

section Block

variable {a M : ℕ}

/-- The matrix `W` with the columns `V_k`. -/
def colMat (V : Fin a → Fin M → ℝ) : Matrix (Fin M) (Fin a) ℝ := Matrix.of fun r j => V j r

/-- The block matrix `[[1, 0], [W, B]]` of size `a + M`, where the columns of `W` are `V_k`. -/
def blockLower (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    Matrix (Fin (a + M)) (Fin (a + M)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 (colMat V) B)

theorem colMat_mul_transpose_of (l : ℕ) (V : Fin a → Fin M → ℝ) :
    colMat V * (colMat V)ᵀ -
        colMat (fun j r => if l ≤ (j : ℕ) then V j r else 0) *
          (colMat (fun j r => if l ≤ (j : ℕ) then V j r else 0))ᵀ = colGram l V := by
  ext p q
  simp only [colMat, Matrix.sub_apply, Matrix.mul_apply, transpose_apply, of_apply, colGram,
    Matrix.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < l
  · rw [ite_eq_right (by omega), ite_eq_left hk, vecMulVec_apply]
    ring
  · have hl : l ≤ (k : ℕ) := by omega
    simp only [hl, ite_true, ite_eq_right hk, Matrix.zero_apply]
    ring

theorem colMat_mul_transpose (V : Fin a → Fin M → ℝ) :
    colMat V * (colMat V)ᵀ = colGram a V := by
  have h := colMat_mul_transpose_of a V
  have h0 : colMat (fun j r => if a ≤ (j : ℕ) then V j r else 0) = 0 := by
    ext r j
    simp only [colMat, of_apply, Matrix.zero_apply]
    rw [ite_eq_right (by have := j.2; omega)]
  rw [h0, Matrix.zero_mul, sub_zero] at h
  exact h

theorem blockLower_mul_transpose (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    blockLower V B * (blockLower V B)ᵀ =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks 1 (colMat V)ᵀ (colMat V) (colMat V * (colMat V)ᵀ + B * Bᵀ)) := by
  rw [blockLower, reindex_apply, transpose_submatrix, submatrix_mul_equiv, fromBlocks_transpose,
    fromBlocks_multiply, reindex_apply]
  congr 1
  simp

theorem gram_blockLower_of_le (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ) {l : ℕ}
    (hl : l ≤ a) : gram l (blockLower V B) = (colGram l V + B * Bᵀ).det := by
  set V' : Fin a → Fin M → ℝ := fun j r => if l ≤ (j : ℕ) then V j r else 0 with hV'
  have h : padS l (blockLower V B * (blockLower V B)ᵀ) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks 1 (colMat V')ᵀ (colMat V') (colMat V * (colMat V)ᵀ + B * Bᵀ)) := by
    rw [blockLower_mul_transpose]
    ext p q
    refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
      refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;>
      simp only [padS, of_apply, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Fin.val_castAdd, Fin.val_natAdd, colMat,
        transpose_apply, hV']
    · by_cases hi : l ≤ (i : ℕ)
      · by_cases hj : l ≤ (j : ℕ)
        · rw [ite_eq_left ⟨hi, hj⟩]
        · rw [ite_eq_right (fun h => hj h.2), Matrix.one_apply, Matrix.one_apply]
          simp only [Fin.castAdd_inj]
      · rw [ite_eq_right (fun h => hi h.1), Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.castAdd_inj]
    · by_cases hi : l ≤ (i : ℕ)
      · rw [ite_eq_left ⟨hi, by omega⟩, ite_eq_left hi]
      · rw [ite_eq_right (fun h => hi h.1), ite_eq_right hi, Matrix.one_apply_ne]
        exact fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          omega
    · by_cases hj : l ≤ (j : ℕ)
      · rw [ite_eq_left ⟨by omega, hj⟩, ite_eq_left hj]
      · rw [ite_eq_right (fun h => hj h.2), ite_eq_right hj, Matrix.one_apply_ne]
        exact fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          omega
    · rw [ite_eq_left ⟨by omega, by omega⟩]
  rw [gram_eq_tm, tm, h, det_reindex_self, det_fromBlocks_one₁₁, ← colMat_mul_transpose_of l V]
  congr 1
  abel

theorem gram_blockLower_add (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ) (r : ℕ) :
    gram (a + r) (blockLower V B) = tm r (colGram a V + B * Bᵀ) := by
  have h : padS (a + r) (blockLower V B * (blockLower V B)ᵀ) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks 1 0 0 (padS r (colMat V * (colMat V)ᵀ + B * Bᵀ))) := by
    rw [blockLower_mul_transpose]
    ext p q
    refine Fin.addCases (fun i => ?_) (fun s => ?_) p <;>
      refine Fin.addCases (fun j => ?_) (fun t => ?_) q <;>
      simp only [padS, of_apply, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Fin.val_castAdd, Fin.val_natAdd, Matrix.zero_apply]
    · rw [ite_eq_right (fun h => by have := i.2; omega), Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.castAdd_inj]
    · rw [ite_eq_right (fun h => by have := i.2; omega), Matrix.one_apply_ne]
      exact fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this
        omega
    · rw [ite_eq_right (fun h => by have := j.2; omega), Matrix.one_apply_ne]
      exact fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this
        omega
    · by_cases hst : r ≤ (s : ℕ) ∧ r ≤ (t : ℕ)
      · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left hst]
      · rw [ite_eq_right (fun h => hst ⟨by omega, by omega⟩), ite_eq_right hst,
          Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.natAdd_inj]
  rw [gram_eq_tm, tm, h, det_reindex_self, det_fromBlocks_zero₂₁, det_one, one_mul,
    colMat_mul_transpose]
  rfl

/-- The Gram determinants of `[[1, 0], [T W, B]]` with `B = T κ`,
`κ κᵀ = 1` and `det T² = 1`, at the positions `l ≤ a`. -/
theorem gram_blockLower_conj_of_le {T κ : Matrix (Fin M) (Fin M) ℝ}
    (hκ : κ * κᵀ = 1) (hdet : T.det ^ 2 = 1) (V : Fin a → Fin M → ℝ) {l : ℕ} (hl : l ≤ a) :
    gram l (blockLower (fun k => T *ᵥ V k) (T * κ)) = (1 + colGram l V).det := by
  rw [gram_blockLower_of_le _ _ hl, colGram_mulVec, mul_mul_transpose hκ]
  have : T * colGram l V * Tᵀ + T * Tᵀ = T * (1 + colGram l V) * Tᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, add_comm]
  rw [this, det_mul, det_mul, det_transpose]
  have h2 : T.det * (1 + colGram l V).det * T.det = T.det ^ 2 * (1 + colGram l V).det := by ring
  rw [h2, hdet, one_mul]

/-- The Gram determinants of `[[1, 0], [T W, B]]` with `B = T κ` at the positions `a + r`. -/
theorem gram_blockLower_conj_add {T κ : Matrix (Fin M) (Fin M) ℝ} (hT : T.IsUpperTriangular)
    (hκ : κ * κᵀ = 1) (V : Fin a → Fin M → ℝ) (r : ℕ) :
    gram (a + r) (blockLower (fun k => T *ᵥ V k) (T * κ)) =
      gram r (T * κ) * tm r (1 + colGram a V) := by
  rw [gram_blockLower_add, colGram_mulVec, mul_mul_transpose hκ, gram_mul hT hκ]
  have : T * colGram a V * Tᵀ + T * Tᵀ = T * (1 + colGram a V) * Tᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, add_comm]
  rw [this, tm_conj hT]

end Block

end RealLeviChartGram

end Langlands.Archimedean
