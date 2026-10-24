import Langlands.Group.GL.UpperBruhatPivotStatement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin

namespace Langlands.GeneralLinear

universe u

private theorem pivot_mul_row {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (p : Fin m) (c : Fin m → K) (i j : Fin m) :
    (A * (1 + Matrix.of (fun a b => if a = p then c b else 0))) i j =
      A i j + A i p * c j := by
  rw [Matrix.mul_add, Matrix.mul_one]
  simp [Matrix.mul_apply, mul_ite]

private theorem pivot_col_mul {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (p : Fin m) (c : Fin m → K) (i j : Fin m) :
    ((1 + Matrix.of (fun a b => if b = p then c a else 0)) * A) i j =
      A i j + c i * A p j := by
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, ite_mul]

private theorem pivot_minor_unit {K : Type u} [Field K] {n : ℕ}
    (A : GeneralLinear (n + 1) K) (p : Fin (n + 1))
    (hrow : ∀ j, A (Fin.last n) j = if j = p then 1 else 0)
    (hcol : ∀ i : Fin n, A i.castSucc p = 0) :
    ∃ h : GeneralLinear n K, ∀ i j, A i.castSucc (p.succAbove j) = h i j := by
  classical
  let B : Matrix (Fin n) (Fin n) K := fun i j => A i.castSucc (p.succAbove j)
  let C : Matrix (Fin n) (Fin n) K := fun i j => A.inv (p.succAbove i) j.castSucc
  have hBC : B * C = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K =>
      M i.castSucc j.castSucc) A.val_inv
    rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ p] at h
    simpa [B, C, Matrix.mul_apply, hcol, Matrix.one_apply] using h
  have hCB : C * B = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K =>
      M (p.succAbove i) (p.succAbove j)) A.inv_val
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h
    simpa [B, C, Matrix.mul_apply, hrow, Fin.succAbove_ne, Matrix.one_apply,
      Fin.succAbove_right_inj] using h
  exact ⟨⟨B, C, hBC, hCB⟩, fun _ _ => rfl⟩

/-- The ordered pivot-isolation theorem over every field, including residual rank zero. -/
theorem fieldUpperBruhatPivotTheorem : FieldUpperBruhatPivotTheorem.{u} := by
  classical
  intro K _ n g
  have hex : ∃ j : Fin (n + 1), g (Fin.last n) j ≠ 0 := by
    by_contra! hz
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K =>
      M (Fin.last n) (Fin.last n)) g.val_inv
    simp [Matrix.mul_apply, hz] at h
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => g (Fin.last n) j ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let p := S.min' hS
  have hp : g (Fin.last n) p ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hbefore : ∀ j, j < p → g (Fin.last n) j = 0 := by
    intro j hj
    by_contra hne
    have hle : p ≤ j := Finset.min'_le S j (by simp [S, hne])
    exact (not_lt_of_ge hle) hj
  let a := g (Fin.last n) p
  let c : Fin (n + 1) → K := fun j =>
    if j = p then a⁻¹ - 1 else -(a⁻¹ * g (Fin.last n) j)
  let Rm : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    1 + Matrix.of (fun i j => if i = p then c j else 0)
  have hRt : Rm.IsUpperTriangular := by
    intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    by_cases hi : i = p
    · subst i
      simp [Rm, hne, hne.symm, c, hbefore j hji]
    · simp [Rm, hne, hi]
  have hRd : Rm.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hRt]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hi : i = p
    · subst i
      simpa [Rm, c, a] using inv_ne_zero hp
    · simp [Rm, hi]
  let R : GeneralLinear (n + 1) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Rm hRd
  let q := g * R
  have hq : ∀ j, q (Fin.last n) j = if j = p then 1 else 0 := by
    intro j
    change (g.val * Rm) (Fin.last n) j = _
    rw [pivot_mul_row]
    by_cases hj : j = p
    · subst j
      simp only [c, ite_true]
      dsimp [a]
      field_simp
      ring
    · simp only [c, ite_false, hj]
      dsimp [a]
      field_simp
      ring
  let d : Fin (n + 1) → K := fun i => if i = Fin.last n then 0 else -q i p
  let Lm : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    1 + Matrix.of (fun i j => if j = Fin.last n then d i else 0)
  have hLt : Lm.IsUpperTriangular := by
    intro i j hji
    have hj : j ≠ Fin.last n := by
      intro he
      subst j
      exact (not_lt_of_ge (Fin.le_last i)) hji
    have hne : i ≠ j := ne_of_gt hji
    simp [Lm, hne, hj]
  have hLd : Lm.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hLt]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hi : i = Fin.last n <;> simp [Lm, d, hi]
  let L : GeneralLinear (n + 1) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Lm hLd
  have hprod : ∀ i j, (L * g * R) i j = q i j + d i * q (Fin.last n) j := by
    intro i j
    rw [mul_assoc]
    change (Lm * q.val) i j = _
    exact pivot_col_mul q.val (Fin.last n) d i j
  have hrow : ∀ j, (L * g * R) (Fin.last n) j = if j = p then 1 else 0 := by
    intro j
    simp [hprod, d, hq]
  have hcol : ∀ i : Fin n, (L * g * R) i.castSucc p = 0 := by
    intro i
    simp [hprod, d, hq]
  obtain ⟨h, hh⟩ := pivot_minor_unit (L * g * R) p hrow hcol
  exact ⟨L, R, p, h, hLt, hRt, hrow, hcol, hh⟩

end Langlands.GeneralLinear
