import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Determinants of the classical integral Cartan matrices -/

open Matrix

namespace Langlands.LinearAlgebra

private abbrev tail {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := M.submatrix Fin.succ Fin.succ

private theorem det_of_first_leaf {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ)
    (h00 : M 0 0 = 2)
    (h0 : ∀ i : Fin (n + 1), M 0 i.succ = if i = 0 then -1 else 0)
    (h1 : ∀ i : Fin (n + 1), M i.succ 0 = if i = 0 then -1 else 0) :
    M.det = 2 * (tail M).det - (tail (tail M)).det := by
  let N := M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove
  have hN (i : Fin (n + 1)) : N i 0 = if i = 0 then -1 else 0 := by
    simpa only [N, submatrix_apply, Fin.one_succAbove_zero] using h1 i
  have ht : tail N = tail (tail M) := by
    ext i j
    simp [N, tail]
  have hdet : N.det = -(tail (tail M)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hN, ht, tail]
  have h01 : M 0 1 = -1 := by simpa using h0 0
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [h00, h01, h0, hdet, N, tail, sub_eq_add_neg]

open CartanMatrix in
private theorem tail_A (n : ℕ) : tail (A (n + 1)) = A n := by
  ext i j
  simp only [tail, submatrix_apply, A, of_apply, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> omega

open CartanMatrix in
private theorem tail_B (n : ℕ) : tail (B (n + 1)) = B n := by
  ext i j
  simp only [tail, submatrix_apply, B, of_apply, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> omega

open CartanMatrix in
private theorem tail_D (n : ℕ) (hn : 3 ≤ n) : tail (D (n + 1)) = D n := by
  ext i j
  simp only [tail, submatrix_apply, D, of_apply, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> omega

open CartanMatrix in
private theorem row_zero_A {n : ℕ} (i : Fin (n + 1)) :
    A (n + 2) 0 i.succ = if i = 0 then -1 else 0 := by
  simp only [A, of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
  split_ifs <;> simp_all

open CartanMatrix in
private theorem row_zero_B {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    B (n + 2) 0 i.succ = if i = 0 then -1 else 0 := by
  simp only [B, of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
  split_ifs <;> simp_all

open CartanMatrix in
private theorem column_zero_B {n : ℕ} (i : Fin (n + 1)) :
    B (n + 2) i.succ 0 = if i = 0 then -1 else 0 := by
  simp only [B, of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
  split_ifs <;> simp_all

open CartanMatrix in
private theorem row_zero_D {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) :
    D (n + 2) 0 i.succ = if i = 0 then -1 else 0 := by
  simp only [D, of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
  split_ifs <;> simp_all
  omega

open CartanMatrix in
/-- The determinant of the type-A Cartan matrix of rank `n` is `n + 1`. -/
theorem cartan_A_det (n : ℕ) : (A n).det = (n : ℤ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [A_one, Matrix.det_fin_one_of]; decide
  | more n ih₀ ih₁ =>
    have hcol (i : Fin (n + 1)) : A (n + 2) i.succ 0 = if i = 0 then -1 else 0 :=
      ((A_isSymm (n + 2)).apply _ _).trans (row_zero_A i)
    rw [det_of_first_leaf _ (congrFun (A_diag (n + 2)) 0) row_zero_A hcol,
      tail_A, tail_A, ih₀, ih₁]
    push_cast
    ring

open CartanMatrix in
/-- The determinant of the type-B Cartan matrix of rank at least one is `2`. -/
theorem cartan_B_det {n : ℕ} (hn : 1 ≤ n) : (B n).det = 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction m using Nat.twoStepInduction with
  | zero =>
    change (B 1).det = 2
    rw [B_one, cartan_A_det]
    decide
  | one => rw [show (1 : ℕ) + 1 = 2 by decide, B_two]; decide
  | more m ih₀ ih₁ =>
    change (B ((m + 1) + 2)).det = 2
    rw [det_of_first_leaf _ (B_diag _ 0) (row_zero_B (by omega)) column_zero_B,
      tail_B, tail_B, ih₀, ih₁]
    decide

open CartanMatrix in
/-- The determinant of the type-C Cartan matrix of rank at least one is `2`. -/
theorem cartan_C_det {n : ℕ} (hn : 1 ≤ n) : (C n).det = 2 := by
  rw [← B_transpose, Matrix.det_transpose, cartan_B_det hn]

open CartanMatrix in
/-- The determinant of the type-D Cartan matrix of rank at least three is `4`. -/
theorem cartan_D_det {n : ℕ} (hn : 3 ≤ n) : (D n).det = 4 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction m using Nat.twoStepInduction with
  | zero => rw [Nat.zero_add, D_three]; decide
  | one => rw [show (1 : ℕ) + 3 = 4 by decide, D_four]; decide
  | more m ih₀ ih₁ =>
    change (D ((m + 3) + 2)).det = 4
    have hcol (i : Fin ((m + 3) + 1)) :
        D ((m + 3) + 2) i.succ 0 = if i = 0 then -1 else 0 :=
      ((D_isSymm ((m + 3) + 2)).apply _ _).trans (row_zero_D (by omega) i)
    rw [det_of_first_leaf _ (D_diag _ 0) (row_zero_D (by omega)) hcol,
      tail_D _ (by omega), tail_D _ (by omega), ih₀, ih₁]
    decide

open CartanMatrix in
/-- The determinant formulas for the four classical Cartan families. -/
def ClassicalCartanDeterminantsStatement : Prop :=
  (∀ n : ℕ, (A n).det = (n : ℤ) + 1) ∧
    (∀ n : ℕ, 1 ≤ n → (B n).det = 2) ∧
    (∀ n : ℕ, 1 ≤ n → (C n).det = 2) ∧
    (∀ n : ℕ, 3 ≤ n → (D n).det = 4)

theorem classicalCartanDeterminants : ClassicalCartanDeterminantsStatement :=
  ⟨cartan_A_det, fun _ => cartan_B_det, fun _ => cartan_C_det, fun _ => cartan_D_det⟩

end Langlands.LinearAlgebra
