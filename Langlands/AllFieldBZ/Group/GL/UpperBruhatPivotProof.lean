import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Group.GL.UpperBruhatPivotProof

/-!
# All-field port of `Langlands.Group.GL.UpperBruhatPivotProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.UpperBruhatPivotProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
universe u

private theorem _root_.Langlands.GeneralLinear.pivot_mul_row {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (p : Fin m) (c : Fin m → K) (i j : Fin m) :
    (A * (1 + Matrix.of (fun a b => if a = p then c b else 0))) i j =
      A i j + A i p * c j := by
  rw [Matrix.mul_add, Matrix.mul_one]
  simp [Matrix.mul_apply, mul_ite]

private theorem _root_.Langlands.GeneralLinear.pivot_col_mul {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (p : Fin m) (c : Fin m → K) (i j : Fin m) :
    ((1 + Matrix.of (fun a b => if b = p then c a else 0)) * A) i j =
      A i j + c i * A p j := by
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, ite_mul]

private theorem _root_.Langlands.GeneralLinear.pivot_minor_unit {K : Type u} [Field K] {n : ℕ}
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

end Langlands.AllFieldBZ.GeneralLinear
