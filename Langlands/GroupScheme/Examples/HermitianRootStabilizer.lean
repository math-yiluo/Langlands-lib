import Langlands.GroupScheme.Examples.HermitianRootLeviGeneration

/-! # Reduction of the anisotropic Hermitian top-line stabilizer to the Levi -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] [DecidableEq ι] {c : RingInvolution L}
  {H : DiagonalForm c ι}

/-- A last column with nonzero bottom entry determines an upper root parameter. -/
def lastColumnParameter (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex bottomIndex ≠ 0) : Parameters H :=
  ⟨(fun k => c.bar (M (middleIndex k) bottomIndex / M bottomIndex bottomIndex),
      M topIndex bottomIndex / M bottomIndex bottomIndex), by
    have hbar : c.bar (M bottomIndex bottomIndex) ≠ 0 := by simpa using hd
    have hp :
        H.pairing
            (fun k => c.bar (M (middleIndex k) bottomIndex / M bottomIndex bottomIndex))
            (fun k => c.bar (M (middleIndex k) bottomIndex / M bottomIndex bottomIndex)) =
          (∑ k, H.weight k * c.bar (M (middleIndex k) bottomIndex) *
              M (middleIndex k) bottomIndex) /
            (c.bar (M bottomIndex bottomIndex) * M bottomIndex bottomIndex) := by
      simp only [DiagonalForm.pairing, RingInvolution.bar_bar, map_div₀]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp]
    simp only [map_div₀]
    have h := preservesForm_entry hM bottomIndex bottomIndex
    simp [gram, bottomIndex, Matrix.fromBlocks] at h
    field_simp
    linear_combination h⟩

@[simp] theorem lastColumnParameter_vector (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex bottomIndex ≠ 0) (k : ι) :
    (lastColumnParameter M hM hd).vector k =
      c.bar (M (middleIndex k) bottomIndex / M bottomIndex bottomIndex) := rfl

@[simp] theorem lastColumnParameter_scalar (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex bottomIndex ≠ 0) :
    (lastColumnParameter M hM hd).scalar =
      M topIndex bottomIndex / M bottomIndex bottomIndex := rfl

theorem lastColumn_eq_root_column (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex bottomIndex ≠ 0) (i : Index ι) :
    M i bottomIndex = Parameters.matrix (lastColumnParameter M hM hd) i bottomIndex *
      M bottomIndex bottomIndex := by
  rcases i with i | i | i <;>
    simp [Parameters.matrix, Matrix.fromBlocks, topIndex, middleIndex, bottomIndex, hd]

theorem lastColumn_inverse_root (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex bottomIndex ≠ 0) (i : Index ι) :
    (Parameters.matrix (lastColumnParameter M hM hd)⁻¹ * M) i bottomIndex =
      (if i = bottomIndex then M bottomIndex bottomIndex else 0) := by
  let x := lastColumnParameter M hM hd
  have hcol : ∀ k, M k bottomIndex = Parameters.matrix x k bottomIndex *
      M bottomIndex bottomIndex := lastColumn_eq_root_column M hM hd
  calc
    _ = ∑ k, Parameters.matrix x⁻¹ i k *
        (Parameters.matrix x k bottomIndex * M bottomIndex bottomIndex) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [hcol k]
    _ = (Parameters.matrix x⁻¹ * Parameters.matrix x) i bottomIndex *
        M bottomIndex bottomIndex := by
      simp only [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
    _ = (1 : Matrix (Index ι) (Index ι) L) i bottomIndex *
        M bottomIndex bottomIndex := by
      rw [← Parameters.matrix_mul, inv_mul_cancel, Parameters.matrix_one]
    _ = _ := by simp [Matrix.one_apply, ite_mul]

theorem firstColumn_on_top_of_bottom_eq_zero (hH : H.IsAnisotropic)
    {M : Matrix (Index ι) (Index ι) L} (hM : PreservesForm H M)
    (hd : M bottomIndex topIndex = 0) (i : Index ι) :
    M i topIndex = if i = topIndex then M topIndex topIndex else 0 := by
  have hnorm : H.pairing (fun k => M (middleIndex k) topIndex)
      (fun k => M (middleIndex k) topIndex) = 0 := by
    have h := preservesForm_entry hM topIndex topIndex
    simpa [hd, gram, topIndex, Matrix.fromBlocks, DiagonalForm.pairing,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hm := hH _ hnorm
  rcases i with i | i | i
  · simp [topIndex]
  · simpa [middleIndex, topIndex] using congrFun hm i
  · simpa [topIndex, bottomIndex] using hd

theorem top_entry_ne_zero_of_axis_firstColumn
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hcol : ∀ i, g i topIndex = if i = topIndex then g topIndex topIndex else 0) :
    g topIndex topIndex ≠ 0 := by
  intro hz
  apply g.det_ne_zero
  apply Matrix.det_eq_zero_of_column_eq_zero topIndex
  intro i
  rw [hcol i]
  simp [hz]

theorem bottom_entry_of_axis_firstColumn
    {M : Matrix (Index ι) (Index ι) L} (hM : PreservesForm H M)
    (hcol : ∀ i, M i topIndex = if i = topIndex then M topIndex topIndex else 0) :
    M bottomIndex bottomIndex = (c.bar (M topIndex topIndex))⁻¹ := by
  have h := preservesForm_entry hM topIndex bottomIndex
  have hmid (k : ι) : M (middleIndex k) topIndex = 0 := by
    simpa [middleIndex, topIndex] using hcol (middleIndex k)
  have hbot : M bottomIndex topIndex = 0 := by
    simpa [bottomIndex, topIndex] using hcol bottomIndex
  have heq : c.bar (M topIndex topIndex) * M bottomIndex bottomIndex = 1 := by
    simpa [hmid, hbot, gram, Matrix.fromBlocks, topIndex, bottomIndex] using h
  exact eq_inv_of_mul_eq_one_right heq

theorem eq_leviMatrix_of_axis_columns
    {M : Matrix (Index ι) (Index ι) L} (hM : PreservesForm H M)
    (ha : M topIndex topIndex ≠ 0)
    (hcol : ∀ i, M i topIndex = if i = topIndex then M topIndex topIndex else 0)
    (hlast : ∀ i, M i bottomIndex =
      if i = bottomIndex then M bottomIndex bottomIndex else 0) :
    M = leviMatrix (c := c) (M topIndex topIndex)
      (fun i j => M (middleIndex i) (middleIndex j)) := by
  have hd := bottom_entry_of_axis_firstColumn hM hcol
  have hdne : M bottomIndex bottomIndex ≠ 0 := by
    rw [hd]
    simpa using ha
  have hbar : c.bar (M topIndex topIndex) ≠ 0 := by simpa using ha
  have hbbar : c.bar (M bottomIndex bottomIndex) ≠ 0 := by simpa using hdne
  have hm (k : ι) : M (middleIndex k) topIndex = 0 := by
    simpa [middleIndex, topIndex] using hcol (middleIndex k)
  have hmb (k : ι) : M (middleIndex k) bottomIndex = 0 := by
    simpa [middleIndex, bottomIndex] using hlast (middleIndex k)
  have hbt : M bottomIndex topIndex = 0 := by
    simpa [bottomIndex, topIndex] using hcol bottomIndex
  have htb : M topIndex bottomIndex = 0 := by
    simpa [bottomIndex, topIndex] using hlast topIndex
  have hbm (j : ι) : M bottomIndex (middleIndex j) = 0 := by
    have h := preservesForm_entry hM topIndex (middleIndex j)
    have heq : c.bar (M topIndex topIndex) * M bottomIndex (middleIndex j) = 0 := by
      simpa [hbt, hm, gram, Matrix.fromBlocks, topIndex, middleIndex] using h
    exact (mul_eq_zero.mp heq).resolve_left hbar
  have htm (j : ι) : M topIndex (middleIndex j) = 0 := by
    have h := preservesForm_entry hM bottomIndex (middleIndex j)
    have heq : c.bar (M bottomIndex bottomIndex) * M topIndex (middleIndex j) = 0 := by
      simpa [htb, hmb, gram, Matrix.fromBlocks, bottomIndex, middleIndex] using h
    exact (mul_eq_zero.mp heq).resolve_left hbbar
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [leviMatrix, Matrix.fromBlocks, topIndex, middleIndex,
      hm, hmb, hbt, htb, hbm, htm, hd]

/-- Inverse multiplication by the recovered upper root leaves an actual Levi matrix. -/
theorem exists_root_reduction_to_levi (hH : H.IsAnisotropic)
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hg : g ∈ unitarySubgroup H) (hd : g bottomIndex topIndex = 0) :
    ∃ x : Parameters H, ∃ a : L, a ≠ 0 ∧ ∃ T : Matrix ι ι L,
      (((Parameters.embedding H x)⁻¹ * g : Matrix.GeneralLinearGroup (Index ι) L) :
        Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a T := by
  have hcol := firstColumn_on_top_of_bottom_eq_zero hH hg hd
  have ha := top_entry_ne_zero_of_axis_firstColumn g hcol
  have hdval := bottom_entry_of_axis_firstColumn hg hcol
  have hdne : g bottomIndex bottomIndex ≠ 0 := by
    rw [hdval]
    simpa using ha
  let x := lastColumnParameter (g : Matrix (Index ι) (Index ι) L) hg hdne
  let h := (Parameters.embedding H x)⁻¹ * g
  have hh : h ∈ unitarySubgroup H :=
    (unitarySubgroup H).mul_mem
      ((unitarySubgroup H).inv_mem (Parameters.matrix_preservesForm x)) hg
  have hhval : (h : Matrix (Index ι) (Index ι) L) = Parameters.matrix x⁻¹ *
      (g : Matrix (Index ι) (Index ι) L) := by
    change (((Parameters.embedding H x)⁻¹ : Matrix.GeneralLinearGroup (Index ι) L) :
      Matrix (Index ι) (Index ι) L) * (g : Matrix (Index ι) (Index ι) L) = _
    rw [← (Parameters.embedding H).map_inv]
    rfl
  have hfirst (i : Index ι) : h i topIndex =
      if i = topIndex then g topIndex topIndex else 0 := by
    rw [hhval, Matrix.mul_apply]
    calc
      _ = ∑ k, Parameters.matrix x⁻¹ i k *
          (if k = topIndex then g topIndex topIndex else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hcol k]
      _ = _ := by
        rcases i with i | i | i <;>
          simp [Parameters.matrix, Matrix.fromBlocks, topIndex]
  have htop : h topIndex topIndex = g topIndex topIndex := by
    simpa using hfirst topIndex
  have hlast (i : Index ι) : h i bottomIndex =
      if i = bottomIndex then h bottomIndex bottomIndex else 0 := by
    have hlast' (j : Index ι) : h j bottomIndex =
        if j = bottomIndex then g bottomIndex bottomIndex else 0 := by
      rw [hhval]
      exact lastColumn_inverse_root _ hg hdne j
    rw [hlast' i, hlast' bottomIndex]
    simp
  refine ⟨x, h topIndex topIndex, htop ▸ ha,
    (fun i j => h (middleIndex i) (middleIndex j)), ?_⟩
  apply eq_leviMatrix_of_axis_columns hh (htop ▸ ha) _ hlast
  intro i
  rw [hfirst i, htop]

end Langlands.GroupScheme.HermitianRoot
