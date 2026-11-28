import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # Strictly lower triangular bilinear forms for sign extensions -/

noncomputable section

namespace Langlands.Covering.BrylinskiDeligne

open Module

variable {ι Y : Type*} [LinearOrder ι] [AddCommGroup Y]
  (e : Basis ι ℤ Y) (B : LinearMap.BilinForm ℤ Y)

/-- The strictly lower triangular part of `B` in the ordered basis `e`. -/
def strictLowerBilinearForm : LinearMap.BilinForm ℤ Y :=
  e.constr ℤ fun i => e.constr ℤ fun j => if j < i then B (e i) (e j) else 0

theorem strictLowerBilinearForm_apply_basis (i j : ι) :
    strictLowerBilinearForm e B (e i) (e j) = if j < i then B (e i) (e j) else 0 := by
  simp [strictLowerBilinearForm]

/-- The symmetrization of the strictly lower part differs from a symmetric form
with even basis diagonal by an even integer on every pair of lattice points. -/
theorem even_sub_strictLowerBilinearForm
    (hsymm : ∀ x y, B x y = B y x) (hdiag : ∀ i, Even (B (e i) (e i))) (x y : Y) :
    Even (B x y - (strictLowerBilinearForm e B x y + strictLowerBilinearForm e B y x)) := by
  choose half hhalf using hdiag
  let H : LinearMap.BilinForm ℤ Y :=
    e.constr ℤ fun i => e.constr ℤ fun j => if i = j then half i else 0
  let D := strictLowerBilinearForm e B
  have heq : B = D + D.flip + (H + H) := by
    apply LinearMap.ext_basis e e
    intro i j
    change B (e i) (e j) =
      (D (e i) (e j) + D (e j) (e i)) + (H (e i) (e j) + H (e i) (e j))
    rcases lt_trichotomy i j with hij | rfl | hji
    · simpa [D, H, strictLowerBilinearForm_apply_basis, hij, hij.not_gt, hij.ne] using
        hsymm (e i) (e j)
    · simpa [D, H, strictLowerBilinearForm_apply_basis] using hhalf i
    · simp [D, H, strictLowerBilinearForm_apply_basis, hji, hji.not_gt, hji.ne']
  refine ⟨H x y, sub_eq_iff_eq_add.mpr ?_⟩
  have hxy := congrArg (fun C : LinearMap.BilinForm ℤ Y => C x y) heq
  change B x y = (D x y + D y x) + (H x y + H x y) at hxy
  exact hxy.trans (add_comm _ _)

/-- A basis multiple pairs trivially with a sum of basis multiples at later indices. -/
theorem strictLowerBilinearForm_ordered_sum (i : ι) (indices : List ι)
    (h : ∀ j ∈ indices, i ≤ j) (n : ι → ℤ) :
    strictLowerBilinearForm e B (n i • e i) (indices.map fun j => n j • e j).sum = 0 := by
  induction indices with
  | nil => simp
  | cons j indices ih =>
    rw [List.map_cons, List.sum_cons, map_add,
      ih (fun k hk => h k (List.mem_cons_of_mem j hk))]
    have hij := h j List.mem_cons_self
    simp [strictLowerBilinearForm_apply_basis, not_lt_of_ge hij]

/-- Summing the basis coordinates in increasing index order reconstructs the point. -/
theorem sorted_sum_basis_repr [Fintype ι] (y : Y) :
    ((Finset.univ.sort (· ≤ ·)).map fun i => e.repr y i • e i).sum = y := by
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact e.sum_repr y

end Langlands.Covering.BrylinskiDeligne
