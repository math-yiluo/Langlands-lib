import Langlands.GroupScheme.Examples.HermitianRootMiddleGeneration

/-! # Elementary generation of prescribed Hermitian Levi elements -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] [DecidableEq ι] {c : RingInvolution L}
  {H : DiagonalForm c ι}

theorem leviMatrix_det (a : L) (T : Matrix ι ι L) :
    (leviMatrix (c := c) a T).det = a * (T.det * (c.bar a)⁻¹) := by
  simp only [leviMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique,
    Matrix.of_apply]

/-- The nonzero scalar used to adjust one Levi lift to another. -/
def leviScalarAdjustment (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) : Lˣ :=
  Units.mk0 (a / b) (div_ne_zero ha hb)

@[simp] theorem leviScalarAdjustment_val (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) :
    (leviScalarAdjustment a b ha hb : L) = a / b := rfl

theorem leviScalarAdjustment_fixed {a b : L} (ha : a ≠ 0) (hb : b ≠ 0)
    (T : Matrix ι ι L)
    (haT : (leviMatrix (c := c) a T).det = 1)
    (hbT : (leviMatrix (c := c) b T).det = 1) :
    c.bar (leviScalarAdjustment a b ha hb : L) =
      (leviScalarAdjustment a b ha hb : L) := by
  have hbara : c.bar a ≠ 0 := by simpa using ha
  have hbarb : c.bar b ≠ 0 := by simpa using hb
  have ha' : a * T.det = c.bar a := by
    apply (div_eq_one_iff_eq hbara).mp
    simpa only [leviMatrix_det, div_eq_mul_inv, mul_assoc] using haT
  have hb' : b * T.det = c.bar b := by
    apply (div_eq_one_iff_eq hbarb).mp
    simpa only [leviMatrix_det, div_eq_mul_inv, mul_assoc] using hbT
  simp only [leviScalarAdjustment_val, map_div₀]
  apply (div_eq_div_iff hbarb hb).2
  rw [← ha', ← hb']
  ring

omit [Fintype ι] in
theorem diagonalMatrix_eq_leviMatrix (r : Lˣ) (hr : c.bar (r : L) = r) :
    diagonalMatrix (ι := ι) r = leviMatrix (c := c) (r : L) 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [diagonalMatrix, diagonalWeight, leviMatrix, Matrix.fromBlocks,
      Matrix.diagonal_apply, Matrix.one_apply, hr]

/-- Every actual determinant-one Levi element belongs to the subgroup generated
by the two root images under the anisotropy and trace-zero hypotheses. -/
theorem specialUnitary_levi_mem_elementarySubgroup (hH : H.IsAnisotropic)
    (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hg : g ∈ specialUnitarySubgroup H) (a : L) (ha : a ≠ 0)
    (T : Matrix ι ι L)
    (hval : (g : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a T) :
    g ∈ elementarySubgroup H := by
  have hform : PreservesForm H (leviMatrix (c := c) a T) := hval ▸ hg.1
  obtain ⟨h, hh, b, hb, hhval⟩ :=
    exists_elementary_levi_middle hH s hs hsne T (preservesMiddle_of_levi hform)
  have haT : (leviMatrix (c := c) a T).det = 1 := by
    rw [← hval]
    exact congrArg Units.val hg.2
  have hbT : (leviMatrix (c := c) b T).det = 1 := by
    rw [← hhval]
    exact congrArg Units.val (elementarySubgroup_le_specialUnitarySubgroup H hh).2
  let r := leviScalarAdjustment a b ha hb
  have hr : c.bar (r : L) = r := leviScalarAdjustment_fixed ha hb T haT hbT
  have hdiag := diagonalEmbedding_mem_elementarySubgroup_of_traceZero H s hs hsne r hr
  have hprod : diagonalEmbedding r * h = g := by
    apply Units.ext
    change diagonalMatrix r * (h : Matrix (Index ι) (Index ι) L) =
      (g : Matrix (Index ι) (Index ι) L)
    rw [diagonalMatrix_eq_leviMatrix r hr, hhval, hval, leviMatrix_mul,
      one_mul]
    simp [r, hb]
  rw [← hprod]
  exact (elementarySubgroup H).mul_mem hdiag hh

end Langlands.GroupScheme.HermitianRoot
