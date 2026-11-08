import Langlands.GroupScheme.Examples.HermitianRootStabilizer

/-! # Elementary generation of anisotropic-middle Hermitian special-unitary matrices -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] [DecidableEq ι] {c : RingInvolution L}
  {H : DiagonalForm c ι}

/-- An actual elementary reducer sending the first column onto the top axis. -/
def firstColumnReducer (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (M : Matrix (Index ι) (Index ι) L) (hM : PreservesForm H M)
    (hd : M bottomIndex topIndex ≠ 0) : Matrix.GeneralLinearGroup (Index ι) L :=
  traceZeroReflection H s hs hsne *
    (Parameters.embedding H (firstColumnParameter M hM hd))⁻¹

theorem firstColumnReducer_mem_elementarySubgroup
    (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (M : Matrix (Index ι) (Index ι) L) (hM : PreservesForm H M)
    (hd : M bottomIndex topIndex ≠ 0) :
    firstColumnReducer s hs hsne M hM hd ∈ elementarySubgroup H :=
  (elementarySubgroup H).mul_mem
    (traceZeroReflection_mem_elementarySubgroup H s hs hsne)
    ((elementarySubgroup H).inv_mem (embedding_mem_elementarySubgroup H _))

theorem firstColumnReducer_column
    (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (g : Matrix.GeneralLinearGroup (Index ι) L) (hg : g ∈ unitarySubgroup H)
    (hd : g bottomIndex topIndex ≠ 0) (i : Index ι) :
    (firstColumnReducer s hs hsne (g : Matrix (Index ι) (Index ι) L) hg hd * g)
        i topIndex =
      if i = topIndex then s * g bottomIndex topIndex else 0 := by
  let x := firstColumnParameter (g : Matrix (Index ι) (Index ι) L) hg hd
  change (((traceZeroReflection H s hs hsne * (Parameters.embedding H x)⁻¹) * g :
    Matrix.GeneralLinearGroup (Index ι) L) : Matrix (Index ι) (Index ι) L) i topIndex = _
  rw [← (Parameters.embedding H).map_inv]
  change (((traceZeroReflection H s hs hsne : Matrix (Index ι) (Index ι) L) *
    Parameters.matrix x⁻¹) * (g : Matrix (Index ι) (Index ι) L)) i topIndex = _
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  calc
    _ = ∑ k, (traceZeroReflection H s hs hsne : Matrix (Index ι) (Index ι) L) i k *
        (if k = bottomIndex then g bottomIndex topIndex else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [firstColumn_inverse_root (g : Matrix (Index ι) (Index ι) L) hg hd k]
    _ = _ := by
      rw [traceZeroReflection_val]
      rcases i with i | i | i <;>
        simp [reflectionMatrix, Matrix.fromBlocks, topIndex, bottomIndex]

theorem specialUnitary_mem_elementarySubgroup_of_bottom_eq_zero
    (hH : H.IsAnisotropic) (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hg : g ∈ specialUnitarySubgroup H) (hd : g bottomIndex topIndex = 0) :
    g ∈ elementarySubgroup H := by
  obtain ⟨x, a, ha, T, hval⟩ := exists_root_reduction_to_levi hH g hg.1 hd
  have hx := embedding_mem_specialUnitarySubgroup H x
  have hred := specialUnitary_levi_mem_elementarySubgroup hH s hs hsne
    ((Parameters.embedding H x)⁻¹ * g)
    ((specialUnitarySubgroup H).mul_mem ((specialUnitarySubgroup H).inv_mem hx) hg)
    a ha T hval
  have h := (elementarySubgroup H).mul_mem (embedding_mem_elementarySubgroup H x) hred
  simpa only [mul_inv_cancel_left] using h

/-- Under the supplied anisotropy and trace-zero hypotheses, the two actual root
images generate every special-unitary matrix. -/
theorem specialUnitary_mem_elementarySubgroup_of_traceZero
    (hH : H.IsAnisotropic) (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hg : g ∈ specialUnitarySubgroup H) : g ∈ elementarySubgroup H := by
  by_cases hd : g bottomIndex topIndex = 0
  · exact specialUnitary_mem_elementarySubgroup_of_bottom_eq_zero hH s hs hsne g hg hd
  · let e := firstColumnReducer s hs hsne (g : Matrix (Index ι) (Index ι) L) hg.1 hd
    have he : e ∈ elementarySubgroup H :=
      firstColumnReducer_mem_elementarySubgroup s hs hsne _ hg.1 hd
    have hredSU : e * g ∈ specialUnitarySubgroup H :=
      (specialUnitarySubgroup H).mul_mem
        (elementarySubgroup_le_specialUnitarySubgroup H he) hg
    have hzero : (e * g) bottomIndex topIndex = 0 := by
      simpa [bottomIndex, topIndex] using
        firstColumnReducer_column s hs hsne g hg.1 hd bottomIndex
    have hred := specialUnitary_mem_elementarySubgroup_of_bottom_eq_zero
      hH s hs hsne (e * g) hredSU hzero
    have h := (elementarySubgroup H).mul_mem ((elementarySubgroup H).inv_mem he) hred
    simpa only [inv_mul_cancel_left] using h

theorem elementarySubgroup_eq_specialUnitarySubgroup_of_traceZero
    (hH : H.IsAnisotropic) (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0) :
    elementarySubgroup H = specialUnitarySubgroup H := by
  apply le_antisymm (elementarySubgroup_le_specialUnitarySubgroup H)
  intro g hg
  exact specialUnitary_mem_elementarySubgroup_of_traceZero hH s hs hsne g hg

/-- A nonidentity involution supplies the nonzero trace-zero scalar in every
characteristic, including characteristic two. -/
theorem elementarySubgroup_eq_specialUnitarySubgroup
    (hH : H.IsAnisotropic) (hc : ∃ a : L, c.bar a ≠ a) :
    elementarySubgroup H = specialUnitarySubgroup H := by
  obtain ⟨a, ha⟩ := hc
  apply elementarySubgroup_eq_specialUnitarySubgroup_of_traceZero hH (a - c.bar a)
  · simp only [map_sub, RingInvolution.bar_bar]
    ring
  · exact sub_ne_zero.mpr (Ne.symm ha)

end Langlands.GroupScheme.HermitianRoot
