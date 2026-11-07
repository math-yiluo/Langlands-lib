import Langlands.GroupScheme.Examples.SU3RootElementaryGeneration

/-! # Generation of the actual determinant-one Hermitian matrix subgroup -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u v

section Ring

variable {A : Type u} [CommRing A] (c : RingInvolution A)

@[simp] theorem conjugateTranspose_one :
    conjugateTranspose c (1 : Matrix (Fin 3) (Fin 3) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjugateTranspose]

theorem conjugateTranspose_mul (M N : Matrix (Fin 3) (Fin 3) A) :
    conjugateTranspose c (M * N) = conjugateTranspose c N * conjugateTranspose c M := by
  ext i j
  simp [conjugateTranspose, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem preservesForm_one : PreservesForm c (1 : Matrix (Fin 3) (Fin 3) A) := by
  simp [PreservesForm]

theorem preservesForm_mul {M N : Matrix (Fin 3) (Fin 3) A}
    (hM : PreservesForm c M) (hN : PreservesForm c N) :
    PreservesForm c (M * N) := by
  unfold PreservesForm at *
  rw [conjugateTranspose_mul]
  calc
    _ = conjugateTranspose c N * (conjugateTranspose c M * gram A * M) * N := by
      simp only [Matrix.mul_assoc]
    _ = gram A := by rw [hM, hN]

theorem preservesForm_inv (g : Matrix.GeneralLinearGroup (Fin 3) A)
    (hg : PreservesForm c (g : Matrix (Fin 3) (Fin 3) A)) :
    PreservesForm c (g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) := by
  unfold PreservesForm at *
  calc
    _ = conjugateTranspose c (g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) *
        (conjugateTranspose c (g : Matrix (Fin 3) (Fin 3) A) * gram A *
          (g : Matrix (Fin 3) (Fin 3) A)) *
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) := by rw [hg]
    _ = (conjugateTranspose c
        ((g * g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) :
          Matrix (Fin 3) (Fin 3) A)) * gram A *
        ((g * g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) :
          Matrix (Fin 3) (Fin 3) A) := by
      rw [Units.val_mul, conjugateTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = gram A := by simp

/-- The actual invertible matrices preserving the specified Hermitian form. -/
def unitarySubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 3) A) where
  carrier := {g | PreservesForm c (g : Matrix (Fin 3) (Fin 3) A)}
  one_mem' := preservesForm_one c
  mul_mem' := preservesForm_mul c
  inv_mem' hg := preservesForm_inv c _ hg

@[simp] theorem mem_unitarySubgroup (g : Matrix.GeneralLinearGroup (Fin 3) A) :
    g ∈ unitarySubgroup c ↔ PreservesForm c (g : Matrix (Fin 3) (Fin 3) A) := Iff.rfl

/-- The actual determinant-one subgroup of the specified Hermitian isometry group. -/
def specialUnitarySubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 3) A) :=
  unitarySubgroup c ⊓ (Matrix.GeneralLinearGroup.det).ker

@[simp] theorem mem_specialUnitarySubgroup (g : Matrix.GeneralLinearGroup (Fin 3) A) :
    g ∈ specialUnitarySubgroup c ↔
      PreservesForm c (g : Matrix (Fin 3) (Fin 3) A) ∧
        Matrix.GeneralLinearGroup.det g = 1 := Iff.rfl

theorem embedding_mem_specialUnitarySubgroup (x : Parameters c) :
    Parameters.embedding c x ∈ specialUnitarySubgroup c :=
  ⟨Parameters.matrix_preservesForm x, Parameters.embedding_det x⟩

theorem diagonal_mem_specialUnitarySubgroup (t : Aˣ) :
    diagonal c t ∈ specialUnitarySubgroup c :=
  ⟨diagonal_preservesForm c t, diagonal_det c t⟩

theorem weylElement_mem_specialUnitarySubgroup :
    (weylElement : Matrix.GeneralLinearGroup (Fin 3) A) ∈ specialUnitarySubgroup c :=
  ⟨weylElement_preservesForm c, weylElement_det⟩

theorem oppositeEmbedding_mem_specialUnitarySubgroup (x : Parameters c) :
    oppositeEmbedding c x ∈ specialUnitarySubgroup c := by
  simp only [oppositeEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  exact (specialUnitarySubgroup c).mul_mem
    ((specialUnitarySubgroup c).mul_mem
      (weylElement_mem_specialUnitarySubgroup c)
      (embedding_mem_specialUnitarySubgroup c x))
    ((specialUnitarySubgroup c).inv_mem (weylElement_mem_specialUnitarySubgroup c))

theorem elementarySubgroup_le_specialUnitarySubgroup :
    elementarySubgroup c ≤ specialUnitarySubgroup c := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    exact embedding_mem_specialUnitarySubgroup c x
  · rintro _ ⟨x, rfl⟩
    exact oppositeEmbedding_mem_specialUnitarySubgroup c x

theorem preservesForm_entry {M : Matrix (Fin 3) (Fin 3) A}
    (hM : PreservesForm c M) (i j : Fin 3) :
    c.bar (M 2 i) * M 0 j - c.bar (M 1 i) * M 1 j +
      c.bar (M 0 i) * M 2 j = gram A i j := by
  have h := congrArg (fun N : Matrix (Fin 3) (Fin 3) A => N i j) hM
  simpa [conjugateTranspose, gram, Matrix.mul_apply, Fin.sum_univ_three,
    sub_eq_add_neg] using h

theorem diagonal_mul_entry (t : Aˣ) (g : Matrix.GeneralLinearGroup (Fin 3) A)
    (i j : Fin 3) :
    (diagonal c t * g) i j = (diagonalEntries c t i : A) * g i j := by
  change ((diagonal c t : Matrix (Fin 3) (Fin 3) A) *
    (g : Matrix (Fin 3) (Fin 3) A)) i j = _
  rw [Matrix.mul_apply]
  fin_cases i <;> simp [diagonal_apply, diagonalEntries]

end Ring

section Field

variable {L : Type u} [Field L] {c : RingInvolution L}

theorem mem_elementarySubgroup_of_lowerLeft_eq_zero
    (hc : ∃ a : L, c.bar a ≠ a)
    (g : Matrix.GeneralLinearGroup (Fin 3) L)
    (hg : g ∈ specialUnitarySubgroup c) (h20 : g 2 0 = 0) :
    g ∈ elementarySubgroup c := by
  have h00 := preservesForm_entry c hg.1 0 0
  simp [h20, gram] at h00
  have h10 : g 1 0 = 0 := h00
  have h02 := preservesForm_entry c hg.1 0 2
  have h01 := preservesForm_entry c hg.1 0 1
  simp [h10, h20, gram] at h02 h01
  have ha : g 0 0 ≠ 0 := by
    intro h
    simp [h] at h02
  have hbara : c.bar (g 0 0) ≠ 0 := by simpa using ha
  have h21 : g 2 1 = 0 := h01.resolve_left ha
  have hdet : (g : Matrix (Fin 3) (Fin 3) L).det = 1 :=
    congrArg Units.val hg.2
  simp only [Matrix.det_fin_three, h10, h20, h21, mul_zero, zero_mul,
    add_zero, sub_zero] at hdet
  have h11 : g 1 1 = c.bar (g 0 0) / g 0 0 := by
    apply (mul_left_cancel₀ ha)
    field_simp
    linear_combination (c.bar (g 0 0)) * hdet - (g 0 0 * g 1 1) * h02
  let t : Lˣ := Units.mk0 (g 0 0) ha
  let b := diagonal c t⁻¹ * g
  have hb : b ∈ specialUnitarySubgroup c :=
    (specialUnitarySubgroup c).mul_mem (diagonal_mem_specialUnitarySubgroup c t⁻¹) hg
  have hupper : IsUpperUnipotent (b : Matrix (Fin 3) (Fin 3) L) := by
    constructor
    · intro i
      change (diagonal c t⁻¹ * g) i i = 1
      rw [diagonal_mul_entry]
      fin_cases i
      · simp [diagonalEntries, t, Units.val_inv_eq_inv_val, ha]
      · simp [diagonalEntries, t, Units.val_inv_eq_inv_val, h11]
        field_simp
      · simpa [diagonalEntries, t, Units.val_inv_eq_inv_val, map_inv₀] using h02
    · intro i j hij
      change (diagonal c t⁻¹ * g) i j = 0
      rw [diagonal_mul_entry]
      fin_cases i <;> fin_cases j <;> simp_all
  have hemb : b ∈ (Parameters.embedding c).range :=
    (Parameters.mem_range_embedding b).mpr ⟨hupper, hb.1⟩
  have hbe : b ∈ elementarySubgroup c :=
    (show (Parameters.embedding c).range ≤ elementarySubgroup c from le_sup_left) hemb
  have h := (elementarySubgroup c).mul_mem
    (diagonal_mem_elementarySubgroup hc t) hbe
  simpa only [b, ← mul_assoc, ← diagonal_mul, mul_inv_cancel, diagonal_one, one_mul] using h

/-- A nonzero lower-left entry gives a root parameter from the first isotropic column. -/
def firstColumnParameter
    (g : Matrix.GeneralLinearGroup (Fin 3) L)
    (hg : g ∈ specialUnitarySubgroup c) (h20 : g 2 0 ≠ 0) : Parameters c :=
  ⟨(c.bar (g 1 0 / g 2 0), g 0 0 / g 2 0), by
    have hbar : c.bar (g 2 0) ≠ 0 := by simpa using h20
    have h := preservesForm_entry c hg.1 0 0
    simp [gram] at h
    simp only [map_div₀, RingInvolution.bar_bar]
    field_simp
    linear_combination h⟩

@[simp] theorem firstColumnParameter_first
    (g : Matrix.GeneralLinearGroup (Fin 3) L)
    (hg : g ∈ specialUnitarySubgroup c) (h20 : g 2 0 ≠ 0) :
    (firstColumnParameter g hg h20).first = c.bar (g 1 0 / g 2 0) := rfl

@[simp] theorem firstColumnParameter_second
    (g : Matrix.GeneralLinearGroup (Fin 3) L)
    (hg : g ∈ specialUnitarySubgroup c) (h20 : g 2 0 ≠ 0) :
    (firstColumnParameter g hg h20).second = g 0 0 / g 2 0 := rfl

/-- The explicit upper coordinate and Weyl matrix eliminate the lower-left entry. -/
theorem firstColumn_elimination
    (g : Matrix.GeneralLinearGroup (Fin 3) L)
    (hg : g ∈ specialUnitarySubgroup c) (h20 : g 2 0 ≠ 0) :
    ((weylElement : Matrix.GeneralLinearGroup (Fin 3) L) *
      (Parameters.embedding c (firstColumnParameter g hg h20))⁻¹ * g) 2 0 = 0 := by
  have hbar : c.bar (g 2 0) ≠ 0 := by simpa using h20
  have h := preservesForm_entry c hg.1 0 0
  simp [gram] at h
  rw [← (Parameters.embedding c).map_inv]
  change (gram L * Parameters.matrix (firstColumnParameter g hg h20)⁻¹ *
    (g : Matrix (Fin 3) (Fin 3) L)) 2 0 = 0
  simp [gram, Parameters.matrix, Matrix.mul_apply, Fin.sum_univ_three, map_div₀]
  field_simp
  linear_combination h

/-- Every determinant-one Hermitian isometry is generated by the two actual root ranges. -/
theorem specialUnitarySubgroup_le_elementarySubgroup
    (hc : ∃ a : L, c.bar a ≠ a) :
    specialUnitarySubgroup c ≤ elementarySubgroup c := by
  intro g hg
  by_cases h20 : g 2 0 = 0
  · exact mem_elementarySubgroup_of_lowerLeft_eq_zero hc g hg h20
  · let x := firstColumnParameter g hg h20
    let b : Matrix.GeneralLinearGroup (Fin 3) L :=
      weylElement * (Parameters.embedding c x)⁻¹ * g
    have hb : b ∈ specialUnitarySubgroup c :=
      (specialUnitarySubgroup c).mul_mem
        ((specialUnitarySubgroup c).mul_mem
          (weylElement_mem_specialUnitarySubgroup c)
          ((specialUnitarySubgroup c).inv_mem (embedding_mem_specialUnitarySubgroup c x))) hg
    have hb20 : b 2 0 = 0 := firstColumn_elimination g hg h20
    have hbe := mem_elementarySubgroup_of_lowerLeft_eq_zero hc b hb hb20
    have he := (elementarySubgroup c).mul_mem
      (embedding_mem_elementarySubgroup c x)
      ((elementarySubgroup c).mul_mem (weylElement_mem_elementarySubgroup hc) hbe)
    simpa only [b, ← mul_assoc, weylElement_mul_self, mul_one, mul_inv_cancel, one_mul] using he

/-- The specified special unitary subgroup equals its two-root generated subgroup. -/
theorem specialUnitarySubgroup_eq_elementarySubgroup
    (hc : ∃ a : L, c.bar a ≠ a) :
    specialUnitarySubgroup c = elementarySubgroup c :=
  le_antisymm (specialUnitarySubgroup_le_elementarySubgroup hc)
    (elementarySubgroup_le_specialUnitarySubgroup c)

end Field

section Quadratic

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Full generation for the canonical involution of a separable quadratic field extension. -/
theorem specialUnitarySubgroup_eq_elementarySubgroup_quadratic :
    specialUnitarySubgroup (fieldInvolution k L) =
      elementarySubgroup (fieldInvolution k L) :=
  specialUnitarySubgroup_eq_elementarySubgroup (fieldInvolution_exists_nonfixed k L)

end Quadratic

end Langlands.GroupScheme.SU3Root
