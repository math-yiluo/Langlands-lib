import Langlands.GroupScheme.Examples.SU3RootDiagonalAction

/-! # Explicit opposite factors for quadratic root matrices -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u

section Ring

variable {A : Type u} [CommRing A]

/-- The determinant-one anti-diagonal involution for the split Hermitian form. -/
def weylElement : Matrix.GeneralLinearGroup (Fin 3) A where
  val := gram A
  inv := gram A
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem weylElement_val :
    (weylElement (A := A) : Matrix (Fin 3) (Fin 3) A) = gram A := rfl

@[simp] theorem weylElement_inv :
    (weylElement : Matrix.GeneralLinearGroup (Fin 3) A)⁻¹ = weylElement := rfl

@[simp] theorem weylElement_mul_self :
    (weylElement : Matrix.GeneralLinearGroup (Fin 3) A) * weylElement = 1 := by
  simpa only [weylElement_inv] using
    inv_mul_cancel (weylElement : Matrix.GeneralLinearGroup (Fin 3) A)

@[simp] theorem weylElement_det :
    Matrix.GeneralLinearGroup.det (weylElement : Matrix.GeneralLinearGroup (Fin 3) A) = 1 := by
  apply Units.ext
  change (gram A).det = 1
  simp [gram, Matrix.det_fin_three]

theorem weylElement_preservesForm (c : RingInvolution A) :
    PreservesForm c (weylElement (A := A) : Matrix (Fin 3) (Fin 3) A) := by
  unfold PreservesForm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugateTranspose, gram, Matrix.mul_apply, Fin.sum_univ_three]

/-- The actual opposite coordinate subgroup, conjugated by the anti-diagonal involution. -/
def oppositeEmbedding (c : RingInvolution A) :
    Parameters c →* Matrix.GeneralLinearGroup (Fin 3) A :=
  (MulAut.conj weylElement).toMonoidHom.comp (Parameters.embedding c)

theorem oppositeEmbedding_val (c : RingInvolution A) (x : Parameters c) :
    (oppositeEmbedding c x : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -c.bar x.first, 1, 0; x.second, -x.first, 1] := by
  change gram A * Parameters.matrix x * gram A = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, Parameters.matrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- A unit second-coordinate parameter determines an actual monomial matrix. -/
def reflectionMatrix (c : RingInvolution A) (t : Aˣ) :
    Matrix.GeneralLinearGroup (Fin 3) A :=
  diagonal c t * weylElement

theorem reflectionMatrix_val (c : RingInvolution A) (t : Aˣ) :
    (reflectionMatrix c t : Matrix (Fin 3) (Fin 3) A) =
      !![0, 0, (t : A); 0, -(barUnit c t * t⁻¹ : Aˣ), 0;
        ((barUnit c t)⁻¹ : Aˣ), 0, 0] := by
  change (diagonal c t : Matrix (Fin 3) (Fin 3) A) * gram A = _
  rw [diagonal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem reflectionMatrix_det (c : RingInvolution A) (t : Aˣ) :
    Matrix.GeneralLinearGroup.det (reflectionMatrix c t) = 1 := by
  simp [reflectionMatrix]

/-- The ratio of two reflection matrices is the diagonal with the parameter ratio. -/
theorem reflectionMatrix_mul_inv (c : RingInvolution A) (s t : Aˣ) :
    reflectionMatrix c s * (reflectionMatrix c t)⁻¹ = diagonal c (s * t⁻¹) := by
  unfold reflectionMatrix
  rw [mul_inv_rev, mul_assoc, ← mul_assoc weylElement, mul_inv_cancel,
    one_mul, ← diagonal_inv, ← diagonal_mul]

end Ring

section Field

variable {L : Type u} [Field L] {c : RingInvolution L}

namespace Parameters

/-- The left opposite coordinate in the rank-one factorization. -/
def leftOppositeParameter (x : Parameters c) (hx : x.second ≠ 0) : Parameters c :=
  ⟨(x.first / c.bar x.second, (c.bar x.second)⁻¹), by
    have hbar : c.bar x.second ≠ 0 := by simpa using hx
    simp only [map_inv₀, map_div₀, RingInvolution.bar_bar]
    field_simp
    linear_combination x.equation⟩

/-- The right opposite coordinate in the rank-one factorization. -/
def rightOppositeParameter (x : Parameters c) (hx : x.second ≠ 0) : Parameters c :=
  ⟨(x.first / x.second, (c.bar x.second)⁻¹), by
    have hbar : c.bar x.second ≠ 0 := by simpa using hx
    simp only [map_inv₀, map_div₀, RingInvolution.bar_bar]
    field_simp
    linear_combination x.equation⟩

@[simp] theorem leftOppositeParameter_first (x : Parameters c) (hx : x.second ≠ 0) :
    (leftOppositeParameter x hx).first = x.first / c.bar x.second := rfl

@[simp] theorem leftOppositeParameter_second (x : Parameters c) (hx : x.second ≠ 0) :
    (leftOppositeParameter x hx).second = (c.bar x.second)⁻¹ := rfl

@[simp] theorem rightOppositeParameter_first (x : Parameters c) (hx : x.second ≠ 0) :
    (rightOppositeParameter x hx).first = x.first / x.second := rfl

@[simp] theorem rightOppositeParameter_second (x : Parameters c) (hx : x.second ≠ 0) :
    (rightOppositeParameter x hx).second = (c.bar x.second)⁻¹ := rfl

end Parameters

/-- Explicit opposite factors give the actual monomial reflection representative. -/
theorem opposite_factorization (x : Parameters c) (hx : x.second ≠ 0) :
    oppositeEmbedding c (Parameters.leftOppositeParameter x hx) *
        Parameters.embedding c x *
        oppositeEmbedding c (Parameters.rightOppositeParameter x hx) =
      reflectionMatrix c (Units.mk0 x.second hx) := by
  have hbar : c.bar x.second ≠ 0 := by simpa using hx
  apply Units.ext
  change (oppositeEmbedding c (Parameters.leftOppositeParameter x hx) :
      Matrix (Fin 3) (Fin 3) L) * Parameters.matrix x *
      (oppositeEmbedding c (Parameters.rightOppositeParameter x hx) :
        Matrix (Fin 3) (Fin 3) L) =
    (reflectionMatrix c (Units.mk0 x.second hx) : Matrix (Fin 3) (Fin 3) L)
  rw [oppositeEmbedding_val, oppositeEmbedding_val, reflectionMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Parameters.matrix, Matrix.mul_apply, Fin.sum_univ_three,
      map_div₀, barUnit, Units.val_inv_eq_inv_val] <;>
    field_simp <;>
    first
    | (solve | ring)
    | linear_combination x.equation
    | linear_combination -x.equation
    | linear_combination x.first * x.equation
    | linear_combination -x.first * x.equation
    | linear_combination (c.bar x.first) * x.equation
    | linear_combination -(c.bar x.first) * x.equation

end Field

end Langlands.GroupScheme.SU3Root
