import Langlands.GroupScheme.Examples.HermitianRootMatrixStructure

/-! # Unitary subgroups and opposite Hermitian root matrices -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {A : Type u} {ι : Type v}
  [CommRing A] [Fintype ι] [DecidableEq ι] {c : RingInvolution A}

omit [Fintype ι] in
@[simp] theorem conjugateTranspose_one :
    conjugateTranspose c (1 : Matrix (Index ι) (Index ι) A) = 1 := by
  ext i j
  simp [conjugateTranspose, Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem conjugateTranspose_mul (M N : Matrix (Index ι) (Index ι) A) :
    conjugateTranspose c (M * N) = conjugateTranspose c N * conjugateTranspose c M := by
  simp only [conjugateTranspose, Matrix.map_mul, Matrix.transpose_mul]

theorem preservesForm_one (H : DiagonalForm c ι) :
    PreservesForm H (1 : Matrix (Index ι) (Index ι) A) := by
  simp [PreservesForm]

theorem preservesForm_mul {H : DiagonalForm c ι}
    {M N : Matrix (Index ι) (Index ι) A}
    (hM : PreservesForm H M) (hN : PreservesForm H N) :
    PreservesForm H (M * N) := by
  unfold PreservesForm at *
  rw [conjugateTranspose_mul]
  calc
    _ = conjugateTranspose c N * (conjugateTranspose c M * gram H * M) * N := by
      simp only [Matrix.mul_assoc]
    _ = gram H := by rw [hM, hN]

theorem preservesForm_inv {H : DiagonalForm c ι}
    (g : Matrix.GeneralLinearGroup (Index ι) A)
    (hg : PreservesForm H (g : Matrix (Index ι) (Index ι) A)) :
    PreservesForm H (g⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) := by
  unfold PreservesForm at *
  calc
    _ = conjugateTranspose c (g⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) *
        (conjugateTranspose c (g : Matrix (Index ι) (Index ι) A) * gram H *
          (g : Matrix (Index ι) (Index ι) A)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) := by rw [hg]
    _ = conjugateTranspose c
        ((g * g⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) * gram H *
        ((g * g⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) := by
      rw [Units.val_mul, conjugateTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = gram H := by simp

/-- The actual invertible matrices preserving the specified Hermitian form. -/
def unitarySubgroup (H : DiagonalForm c ι) :
    Subgroup (Matrix.GeneralLinearGroup (Index ι) A) where
  carrier := {g | PreservesForm H (g : Matrix (Index ι) (Index ι) A)}
  one_mem' := preservesForm_one H
  mul_mem' := preservesForm_mul
  inv_mem' hg := preservesForm_inv _ hg

@[simp] theorem mem_unitarySubgroup (H : DiagonalForm c ι)
    (g : Matrix.GeneralLinearGroup (Index ι) A) :
    g ∈ unitarySubgroup H ↔ PreservesForm H (g : Matrix (Index ι) (Index ι) A) := Iff.rfl

/-- The determinant-one subgroup of the actual Hermitian isometry group. -/
def specialUnitarySubgroup (H : DiagonalForm c ι) :
    Subgroup (Matrix.GeneralLinearGroup (Index ι) A) :=
  unitarySubgroup H ⊓ Matrix.GeneralLinearGroup.det.ker

@[simp] theorem mem_specialUnitarySubgroup (H : DiagonalForm c ι)
    (g : Matrix.GeneralLinearGroup (Index ι) A) :
    g ∈ specialUnitarySubgroup H ↔
      PreservesForm H (g : Matrix (Index ι) (Index ι) A) ∧
        Matrix.GeneralLinearGroup.det g = 1 := Iff.rfl

theorem embedding_mem_specialUnitarySubgroup (H : DiagonalForm c ι) (x : Parameters H) :
    Parameters.embedding H x ∈ specialUnitarySubgroup H :=
  ⟨Parameters.matrix_preservesForm x, Parameters.embedding_det x⟩

theorem diagonalEmbedding_mem_specialUnitarySubgroup (H : DiagonalForm c ι)
    (r : Aˣ) (hr : c.bar (r : A) = r) :
    diagonalEmbedding r ∈ specialUnitarySubgroup H := by
  refine ⟨diagonalMatrix_preservesForm H r hr, ?_⟩
  apply Units.ext
  exact diagonalMatrix_det r

/-- Interchange the hyperbolic top and bottom, fixing the middle coordinates. -/
def swapIndex : Index ι → Index ι :=
  Sum.elim (fun _ => Sum.inr (Sum.inr ()))
    (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun _ => Sum.inl ()))

omit [CommRing A] [Fintype ι] [DecidableEq ι] in
@[simp] theorem swapIndex_swapIndex (i : Index ι) :
    swapIndex (swapIndex i) = i := by
  rcases i with i | i | i <;> rfl

/-- The top-bottom swap matrix, with identity on the middle space. -/
def swapMatrix : Matrix (Index ι) (Index ι) A :=
  Matrix.fromBlocks 0
    (Matrix.of fun _ j => Sum.elim (fun _ => 0) (fun _ => 1) j)
    (Matrix.of fun i _ => Sum.elim (fun _ => 0) (fun _ => 1) i)
    (Matrix.fromBlocks 1 0 0 0)

theorem swapMatrix_mul_apply (M : Matrix (Index ι) (Index ι) A) (i j : Index ι) :
    ((swapMatrix : Matrix (Index ι) (Index ι) A) * M) i j = M (swapIndex i) j := by
  rcases i with i | i | i <;>
    simp [swapMatrix, swapIndex, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_swapMatrix_apply (M : Matrix (Index ι) (Index ι) A) (i j : Index ι) :
    (M * (swapMatrix : Matrix (Index ι) (Index ι) A)) i j = M i (swapIndex j) := by
  rcases j with j | j | j <;>
    simp [swapMatrix, swapIndex, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem swapMatrix_mul_self :
    (swapMatrix : Matrix (Index ι) (Index ι) A) * swapMatrix = 1 := by
  ext i j
  rw [swapMatrix_mul_apply]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [swapMatrix, swapIndex, Matrix.fromBlocks, Matrix.one_apply]

/-- The invertible top-bottom swap. It need not have determinant one. -/
def swapElement : Matrix.GeneralLinearGroup (Index ι) A :=
  ⟨swapMatrix, swapMatrix, swapMatrix_mul_self, swapMatrix_mul_self⟩

@[simp] theorem swapElement_val :
    ((swapElement : Matrix.GeneralLinearGroup (Index ι) A) :
      Matrix (Index ι) (Index ι) A) = swapMatrix := rfl

@[simp] theorem swapElement_inv :
    (swapElement : Matrix.GeneralLinearGroup (Index ι) A)⁻¹ = swapElement := by
  apply Units.ext
  rfl

omit [Fintype ι] in
@[simp] theorem conjugateTranspose_swapMatrix :
    conjugateTranspose c (swapMatrix : Matrix (Index ι) (Index ι) A) = swapMatrix := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [conjugateTranspose, swapMatrix, Matrix.fromBlocks, Matrix.one_apply, eq_comm]

theorem swapMatrix_preservesForm (H : DiagonalForm c ι) :
    PreservesForm H swapMatrix := by
  unfold PreservesForm
  rw [conjugateTranspose_swapMatrix]
  ext i j
  rw [mul_swapMatrix_apply, swapMatrix_mul_apply]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, swapIndex, Matrix.fromBlocks]

theorem swapElement_mem_unitarySubgroup (H : DiagonalForm c ι) :
    swapElement ∈ unitarySubgroup H := swapMatrix_preservesForm H

/-- The opposite root homomorphism, conjugated by the actual top-bottom swap. -/
def oppositeEmbedding (H : DiagonalForm c ι) :
    Parameters H →* Matrix.GeneralLinearGroup (Index ι) A :=
  (MulAut.conj swapElement).toMonoidHom.comp (Parameters.embedding H)

theorem oppositeEmbedding_injective (H : DiagonalForm c ι) :
    Function.Injective (oppositeEmbedding H) :=
  (MulAut.conj swapElement).injective.comp Parameters.embedding_injective

theorem oppositeEmbedding_apply {H : DiagonalForm c ι} (x : Parameters H)
    (i j : Index ι) :
    (oppositeEmbedding H x) i j = Parameters.matrix x (swapIndex i) (swapIndex j) := by
  change ((swapMatrix : Matrix (Index ι) (Index ι) A) * Parameters.matrix x *
    (swapMatrix : Matrix (Index ι) (Index ι) A)) i j = _
  rw [mul_swapMatrix_apply, swapMatrix_mul_apply]

theorem oppositeEmbedding_mem_specialUnitarySubgroup (H : DiagonalForm c ι)
    (x : Parameters H) : oppositeEmbedding H x ∈ specialUnitarySubgroup H := by
  have hx : Parameters.embedding H x ∈ unitarySubgroup H :=
    Parameters.matrix_preservesForm x
  have hu : swapElement * Parameters.embedding H x * swapElement⁻¹ ∈
      unitarySubgroup H := (unitarySubgroup H).mul_mem
    ((unitarySubgroup H).mul_mem (swapElement_mem_unitarySubgroup H)
      hx)
    ((unitarySubgroup H).inv_mem (swapElement_mem_unitarySubgroup H))
  refine ⟨hu, ?_⟩
  change Matrix.GeneralLinearGroup.det (oppositeEmbedding H x) = 1
  simp only [oppositeEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv, Parameters.embedding_det, mul_one, mul_inv_cancel]

/-- The subgroup generated by the upper and lower actual root images. -/
def elementarySubgroup (H : DiagonalForm c ι) :
    Subgroup (Matrix.GeneralLinearGroup (Index ι) A) :=
  (Parameters.embedding H).range ⊔ (oppositeEmbedding H).range

theorem embedding_mem_elementarySubgroup (H : DiagonalForm c ι) (x : Parameters H) :
    Parameters.embedding H x ∈ elementarySubgroup H :=
  (show (Parameters.embedding H).range ≤ elementarySubgroup H from le_sup_left)
    ⟨x, rfl⟩

theorem oppositeEmbedding_mem_elementarySubgroup (H : DiagonalForm c ι)
    (x : Parameters H) : oppositeEmbedding H x ∈ elementarySubgroup H :=
  (show (oppositeEmbedding H).range ≤ elementarySubgroup H from le_sup_right)
    ⟨x, rfl⟩

theorem elementarySubgroup_le_specialUnitarySubgroup (H : DiagonalForm c ι) :
    elementarySubgroup H ≤ specialUnitarySubgroup H := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    exact embedding_mem_specialUnitarySubgroup H x
  · rintro _ ⟨x, rfl⟩
    exact oppositeEmbedding_mem_specialUnitarySubgroup H x

end Langlands.GroupScheme.HermitianRoot
