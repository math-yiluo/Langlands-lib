import Langlands.Group.GL.TriangularParabolic
import Mathlib.GroupTheory.Solvable

namespace Langlands.GeneralLinear.UpperTriangularSolvable

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem leading_mul (g h : upperTriangularSubgroup (n + 1) R) :
    (g.val.val * h.val.val).submatrix Fin.castSucc Fin.castSucc =
      g.val.val.submatrix Fin.castSucc Fin.castSucc *
        h.val.val.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  have hz : h.val (Fin.last n) j.castSucc = 0 :=
    h.property (Fin.castSucc_lt_last j)
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hz]

private theorem leading_one :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix
      Fin.castSucc Fin.castSucc = 1 := by
  ext i j
  simp [Matrix.one_apply]

/-- Restrict an upper triangular unit to its leading principal block. -/
def leading : upperTriangularSubgroup (n + 1) R →*
    upperTriangularSubgroup n R where
  toFun g := ⟨{
    val := g.val.val.submatrix Fin.castSucc Fin.castSucc
    inv := (g⁻¹).val.val.submatrix Fin.castSucc Fin.castSucc
    val_inv := by
      rw [← leading_mul g g⁻¹]
      change ((g * g⁻¹).val.val).submatrix _ _ = 1
      rw [mul_inv_cancel]
      exact leading_one
    inv_val := by
      rw [← leading_mul g⁻¹ g]
      change ((g⁻¹ * g).val.val).submatrix _ _ = 1
      rw [inv_mul_cancel]
      exact leading_one }, by
        intro i j hji
        exact g.property (Fin.castSucc_lt_castSucc_iff.mpr hji)⟩
  map_one' := Subtype.ext (Units.ext leading_one)
  map_mul' g h := Subtype.ext (Units.ext (leading_mul g h))

@[simp] theorem leading_apply (g : upperTriangularSubgroup (n + 1) R) (i j : Fin n) :
    (leading g).val i j = g.val i.castSucc j.castSucc := rfl

private theorem last_diag_mul (g h : upperTriangularSubgroup (n + 1) R) :
    (g * h).val (Fin.last n) (Fin.last n) =
      g.val (Fin.last n) (Fin.last n) * h.val (Fin.last n) (Fin.last n) := by
  change (g.val.val * h.val.val) _ _ = _
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.last n)]
  intro j hj
  have hz : g.val.val (Fin.last n) j = 0 :=
    g.property (lt_of_le_of_ne (Fin.le_last j) hj)
  rw [hz, zero_mul]

/-- The final diagonal entry, with its actual inverse diagonal entry. -/
def lastDiagonal : upperTriangularSubgroup (n + 1) R →* Rˣ where
  toFun g := {
    val := g.val (Fin.last n) (Fin.last n)
    inv := (g⁻¹).val (Fin.last n) (Fin.last n)
    val_inv := by
      rw [← last_diag_mul]
      change (g * g⁻¹).val (Fin.last n) (Fin.last n) = 1
      simp
    inv_val := by
      rw [← last_diag_mul]
      change (g⁻¹ * g).val (Fin.last n) (Fin.last n) = 1
      simp }
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (last_diag_mul g h)

/-- The leading block and final diagonal, whose kernel is the last-column vector group. -/
def leadingWithDiagonal : upperTriangularSubgroup (n + 1) R →*
    upperTriangularSubgroup n R × Rˣ :=
  (leading (R := R) (n := n)).prod (lastDiagonal (R := R) (n := n))

private theorem kernel_leading {g : upperTriangularSubgroup (n + 1) R}
    (hg : g ∈ (leadingWithDiagonal (R := R) (n := n)).ker) (i j : Fin n) :
    g.val i.castSucc j.castSucc = if i = j then 1 else 0 := by
  have h := congrArg (fun a : upperTriangularSubgroup n R × Rˣ => a.1.val i j) hg
  simpa [leadingWithDiagonal, Matrix.one_apply] using h

private theorem kernel_last {g : upperTriangularSubgroup (n + 1) R}
    (hg : g ∈ (leadingWithDiagonal (R := R) (n := n)).ker) :
    g.val (Fin.last n) (Fin.last n) = 1 := by
  have h := congrArg (fun a : upperTriangularSubgroup n R × Rˣ => (a.2 : R)) hg
  simpa [leadingWithDiagonal, lastDiagonal] using h

private theorem kernel_column_mul {g h : upperTriangularSubgroup (n + 1) R}
    (hg : g ∈ (leadingWithDiagonal (R := R) (n := n)).ker)
    (hh : h ∈ (leadingWithDiagonal (R := R) (n := n)).ker) (i : Fin n) :
    (g * h).val i.castSucc (Fin.last n) =
      h.val i.castSucc (Fin.last n) + g.val i.castSucc (Fin.last n) := by
  change (g.val.val * h.val.val) _ _ = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, kernel_leading hg, kernel_last hh]

/-- The kernel is abelian: its free last-column entries add. -/
theorem kernel_comm (g h : (leadingWithDiagonal (R := R) (n := n)).ker) :
    g * h = h * g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (g.val * h.val).val i j = (h.val * g.val).val i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [last_diag_mul, last_diag_mul, kernel_last g.property, kernel_last h.property]
    · exact ((g.val * h.val).property (Fin.castSucc_lt_last j)).trans
        ((h.val * g.val).property (Fin.castSucc_lt_last j)).symm
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [kernel_column_mul g.property h.property,
          kernel_column_mul h.property g.property, add_comm]
    · rw [kernel_leading (mul_mem g.property h.property),
          kernel_leading (mul_mem h.property g.property)]

/-- Invertible upper triangular matrices over any commutative ring form a solvable group. -/
theorem isSolvable (n : ℕ) (R : Type u) [CommRing R] :
    Group.IsSolvable (upperTriangularSubgroup n R) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
      have := ih
      have : Group.IsSolvable (leadingWithDiagonal (R := R) (n := n)).ker :=
        Group.isSolvable_of_comm kernel_comm
      exact Group.isSolvable_of_ker_le_range
        (leadingWithDiagonal (R := R) (n := n)).ker.subtype
        (leadingWithDiagonal (R := R) (n := n)) (by
          intro g hg
          exact ⟨⟨g, hg⟩, rfl⟩)

end Langlands.GeneralLinear.UpperTriangularSolvable
