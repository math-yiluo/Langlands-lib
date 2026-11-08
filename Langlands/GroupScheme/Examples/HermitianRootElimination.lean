import Langlands.GroupScheme.Examples.HermitianRootOpposites

/-! # First-column elimination for the diagonal Hermitian matrix model -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

/-- The top hyperbolic index. -/
abbrev topIndex : Index ι := Sum.inl ()

/-- A middle index. -/
abbrev middleIndex (i : ι) : Index ι := Sum.inr (Sum.inl i)

/-- The bottom hyperbolic index. -/
abbrev bottomIndex : Index ι := Sum.inr (Sum.inr ())

section Ring

variable {A : Type u} {ι : Type v}
  [CommRing A] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {H : DiagonalForm c ι}

/-- The scalar identity for any pair of columns of a form-preserving matrix. -/
theorem preservesForm_entry {M : Matrix (Index ι) (Index ι) A}
    (hM : PreservesForm H M) (i j : Index ι) :
    c.bar (M bottomIndex i) * M topIndex j -
        (∑ k, H.weight k * c.bar (M (middleIndex k) i) * M (middleIndex k) j) +
        c.bar (M topIndex i) * M bottomIndex j = gram H i j := by
  have h := congrArg (fun N : Matrix (Index ι) (Index ι) A => N i j) hM
  simpa [conjugateTranspose, gram, Matrix.fromBlocks, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.diagonal_apply, sub_eq_add_neg, mul_assoc,
    mul_left_comm, add_assoc] using h

end Ring

section Field

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution L} {H : DiagonalForm c ι}

/-- A nonzero bottom-top entry supplies actual root parameters from the first column. -/
def firstColumnParameter (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) : Parameters H :=
  ⟨(fun k => c.bar (M (middleIndex k) topIndex / M bottomIndex topIndex),
      M topIndex topIndex / M bottomIndex topIndex), by
    have hbar : c.bar (M bottomIndex topIndex) ≠ 0 := by simpa using hd
    have hp :
        H.pairing
            (fun k => c.bar (M (middleIndex k) topIndex / M bottomIndex topIndex))
            (fun k => c.bar (M (middleIndex k) topIndex / M bottomIndex topIndex)) =
          (∑ k, H.weight k * c.bar (M (middleIndex k) topIndex) *
              M (middleIndex k) topIndex) /
            (c.bar (M bottomIndex topIndex) * M bottomIndex topIndex) := by
      simp only [DiagonalForm.pairing, RingInvolution.bar_bar, map_div₀]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp]
    simp only [map_div₀]
    have h := preservesForm_entry hM topIndex topIndex
    simp [gram, topIndex, Matrix.fromBlocks] at h
    field_simp
    linear_combination h⟩

@[simp] theorem firstColumnParameter_vector
    (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) (k : ι) :
    (firstColumnParameter M hM hd).vector k =
      c.bar (M (middleIndex k) topIndex / M bottomIndex topIndex) := rfl

@[simp] theorem firstColumnParameter_scalar
    (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) :
    (firstColumnParameter M hM hd).scalar =
      M topIndex topIndex / M bottomIndex topIndex := rfl

/-- The first column is a scalar multiple of the recovered root matrix's last column. -/
theorem firstColumn_eq_root_column
    (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) (i : Index ι) :
    M i topIndex = Parameters.matrix (firstColumnParameter M hM hd) i bottomIndex *
      M bottomIndex topIndex := by
  rcases i with i | i | i <;>
    simp [Parameters.matrix, Matrix.fromBlocks, topIndex, middleIndex, bottomIndex, hd]

/-- The inverse upper root matrix eliminates every first-column entry except the bottom. -/
theorem firstColumn_inverse_root
    (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) (i : Index ι) :
    (Parameters.matrix (firstColumnParameter M hM hd)⁻¹ * M) i topIndex =
      (if i = bottomIndex then M bottomIndex topIndex else 0) := by
  let x := firstColumnParameter M hM hd
  have hcol : ∀ k, M k topIndex = Parameters.matrix x k bottomIndex *
      M bottomIndex topIndex := firstColumn_eq_root_column M hM hd
  calc
    _ = ∑ k, Parameters.matrix x⁻¹ i k *
        (Parameters.matrix x k bottomIndex * M bottomIndex topIndex) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [hcol k]
    _ = (Parameters.matrix x⁻¹ * Parameters.matrix x) i bottomIndex *
        M bottomIndex topIndex := by
      simp only [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
    _ = (1 : Matrix (Index ι) (Index ι) L) i bottomIndex *
        M bottomIndex topIndex := by
      rw [← Parameters.matrix_mul, inv_mul_cancel, Parameters.matrix_one]
    _ = _ := by simp [Matrix.one_apply, ite_mul]

/-- The swap after inverse-root multiplication puts the first column on the top axis. -/
theorem firstColumn_elimination
    (M : Matrix (Index ι) (Index ι) L)
    (hM : PreservesForm H M) (hd : M bottomIndex topIndex ≠ 0) (i : Index ι) :
    ((swapMatrix : Matrix (Index ι) (Index ι) L) *
      Parameters.matrix (firstColumnParameter M hM hd)⁻¹ * M) i topIndex =
      (if i = topIndex then M bottomIndex topIndex else 0) := by
  rw [Matrix.mul_assoc, swapMatrix_mul_apply, firstColumn_inverse_root]
  rcases i with i | i | i <;> simp [swapIndex, topIndex, bottomIndex]

/-- First-column elimination for an actual invertible form-preserving matrix. -/
theorem firstColumn_elimination_GL
    (g : Matrix.GeneralLinearGroup (Index ι) L)
    (hg : g ∈ unitarySubgroup H) (hd : g bottomIndex topIndex ≠ 0) (i : Index ι) :
    ((swapElement : Matrix.GeneralLinearGroup (Index ι) L) *
      (Parameters.embedding H (firstColumnParameter
        (g : Matrix (Index ι) (Index ι) L) hg hd))⁻¹ * g) i topIndex =
      (if i = topIndex then g bottomIndex topIndex else 0) := by
  rw [← (Parameters.embedding H).map_inv]
  exact firstColumn_elimination (g : Matrix (Index ι) (Index ι) L) hg hd i

end Field
end Langlands.GroupScheme.HermitianRoot
