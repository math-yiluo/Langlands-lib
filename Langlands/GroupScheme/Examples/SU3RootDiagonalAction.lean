import Langlands.GroupScheme.Examples.SU3RootScaling
import Langlands.GroupScheme.Examples.SU3RootParametersMatrix
import Mathlib.Algebra.Group.Pi.Units

/-! # The determinant-one diagonal action on quadratic root coordinates -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u v

section Ring

variable {A : Type u} [CommRing A] (c : RingInvolution A)

/-- The specified involution on scalar units. -/
def barUnit : Aˣ →* Aˣ := Units.map c.bar.toMonoidHom

@[simp] theorem barUnit_val (t : Aˣ) :
    (barUnit c t : A) = c.bar (t : A) := rfl

@[simp] theorem barUnit_barUnit (t : Aˣ) : barUnit c (barUnit c t) = t := by
  apply Units.ext
  exact c.bar_bar (t : A)

/-- The root scalar induced by a determinant-one diagonal parameter. -/
def diagonalRootScalar (t : Aˣ) : Aˣ := t * t * (barUnit c t)⁻¹

/-- The three scalar-unit entries of the diagonal matrix. -/
def diagonalEntries (t : Aˣ) : Fin 3 → Aˣ :=
  ![t, barUnit c t * t⁻¹, (barUnit c t)⁻¹]

/-- The invertible diagonal matrix with entries `(t, bar(t)/t, 1/bar(t))`. -/
def diagonal (t : Aˣ) : Matrix.GeneralLinearGroup (Fin 3) A :=
  Units.map (Matrix.diagonalRingHom (Fin 3) A).toMonoidHom
    (MulEquiv.piUnits.symm (diagonalEntries c t))

@[simp] theorem diagonal_apply (t : Aˣ) (i j : Fin 3) :
    diagonal c t i j = if i = j then (diagonalEntries c t i : A) else 0 := rfl

theorem diagonal_val (t : Aˣ) :
    (diagonal c t : Matrix (Fin 3) (Fin 3) A) =
      !![(t : A), 0, 0; 0, (barUnit c t * t⁻¹ : Aˣ), 0;
        0, 0, ((barUnit c t)⁻¹ : Aˣ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalEntries]

@[simp] theorem diagonal_one : diagonal c 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalEntries]

theorem diagonal_mul (s t : Aˣ) : diagonal c (s * t) = diagonal c s * diagonal c t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal_apply, diagonalEntries, Matrix.mul_apply,
      map_mul, mul_assoc, mul_comm, mul_left_comm]

/-- The scalar-unit diagonal parameterization is a group homomorphism. -/
def diagonalHom : Aˣ →* Matrix.GeneralLinearGroup (Fin 3) A where
  toFun := diagonal c
  map_one' := diagonal_one c
  map_mul' := diagonal_mul c

@[simp] theorem diagonal_inv (t : Aˣ) : diagonal c t⁻¹ = (diagonal c t)⁻¹ :=
  (diagonalHom c).map_inv t

@[simp] theorem diagonal_det (t : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagonal c t) = 1 := by
  apply Units.ext
  change (diagonal c t : Matrix (Fin 3) (Fin 3) A).det = 1
  rw [diagonal_val]
  simp [Matrix.det_fin_three, mul_comm, mul_left_comm]

@[simp] theorem barUnit_inv_val (t : Aˣ) :
    (↑((barUnit c t)⁻¹) : A) = c.bar (↑t⁻¹ : A) := rfl

private theorem bar_val_mul_inv (t : Aˣ) :
    c.bar (t : A) * c.bar (↑t⁻¹ : A) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]


theorem diagonal_preservesForm (t : Aˣ) :
    PreservesForm c (diagonal c t : Matrix (Fin 3) (Fin 3) A) := by
  unfold PreservesForm
  rw [diagonal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugateTranspose, gram, Matrix.mul_apply, Fin.sum_univ_three,
      map_mul, mul_assoc, bar_val_mul_inv]

  calc
    _ = ((t : A) * (↑t⁻¹ : A)) *
        (c.bar (t : A) * c.bar (↑t⁻¹ : A)) := by ring
    _ = 1 := by simp [bar_val_mul_inv]

/-- The diagonal root scalar has the same norm as the original parameter. -/
theorem diagonalRootScalar_norm (t : Aˣ) :
    diagonalRootScalar c t * barUnit c (diagonalRootScalar c t) = t * barUnit c t := by
  simp only [diagonalRootScalar, map_mul, map_inv, barUnit_barUnit]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Actual matrix conjugation realizes the intrinsic root-coordinate scaling. -/
theorem diagonal_conjugate_embedding (t : Aˣ) (x : Parameters c) :
    diagonal c t * Parameters.embedding c x * (diagonal c t)⁻¹ =
      Parameters.embedding c (Parameters.scale (diagonalRootScalar c t : A) x) := by
  apply mul_right_cancel (b := diagonal c t)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Units.ext
  change (diagonal c t : Matrix (Fin 3) (Fin 3) A) * Parameters.matrix x =
    Parameters.matrix (Parameters.scale (diagonalRootScalar c t : A) x) *
      (diagonal c t : Matrix (Fin 3) (Fin 3) A)
  rw [diagonal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Parameters.matrix, diagonalRootScalar, barUnit, Matrix.mul_apply,
      Fin.sum_univ_three, map_mul, mul_assoc, mul_comm, mul_left_comm, bar_val_mul_inv]
  have h : c.bar (t : A) * (c.bar (↑t⁻¹ : A) * c.bar x.first) = c.bar x.first := by
    rw [← mul_assoc, bar_val_mul_inv, one_mul]
  rw [h]

/-- These actual diagonal matrices normalize the actual embedded root group. -/
theorem diagonal_mem_normalizer (t : Aˣ) :
    diagonal c t ∈ Subgroup.normalizer (Parameters.embedding c).range := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Parameters.scale (diagonalRootScalar c t : A) x,
      (diagonal_conjugate_embedding c t x).symm⟩
  · rintro ⟨x, hx⟩
    let a := diagonalRootScalar c t
    let y := (Parameters.scaleEquiv (c := c) a).symm x
    have hy : Parameters.scale (a : A) y = x :=
      (Parameters.scaleEquiv a).apply_symm_apply x
    refine ⟨y, ?_⟩
    apply (MulAut.conj (diagonal c t)).injective
    change diagonal c t * Parameters.embedding c y * (diagonal c t)⁻¹ =
      diagonal c t * g * (diagonal c t)⁻¹
    rw [diagonal_conjugate_embedding, hy]
    exact hx

/-- Conjugation of every embedded coordinate subgroup is the image of scaling. -/
theorem map_conj_diagonal (t : Aˣ) (H : Subgroup (Parameters c)) :
    (H.map (Parameters.embedding c)).map (MulAut.conj (diagonal c t)).toMonoidHom =
      (H.map (Parameters.scale (diagonalRootScalar c t : A))).map
        (Parameters.embedding c) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact diagonal_conjugate_embedding c t x

end Ring

section Valuation

variable {L : Type u} [Field L] {c : RingInvolution L}
  (omega : AddValuation L (WithTop ℝ))
  (hinv : ∀ z : L, omega (c.bar z) = omega z)

include hinv in
/-- The root scalar of the special-unitary diagonal has the parameter's value. -/
theorem diagonalRootScalar_value (t : Lˣ) :
    omega (diagonalRootScalar c t : L) = omega (t : L) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (omega.ne_top_iff.mpr t.ne_zero)
  simp only [diagonalRootScalar, Units.val_mul, barUnit_inv_val, omega.map_mul, hinv]
  rw [Units.val_inv_eq_inv_val, omega.map_inv, ← hs]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
    WithTop.coe_inj]
  ring

include hinv in
/-- The matrix-conjugation action raises root depth by the diagonal parameter's value. -/
theorem depthA_diagonal_scale (t : Lˣ) (x : Parameters c) :
    Parameters.depthA omega (Parameters.scale (diagonalRootScalar c t : L) x) =
      omega (t : L) + Parameters.depthA omega x := by
  rw [Parameters.depthA_scale omega hinv, diagonalRootScalar_value omega hinv]

include hinv in
/-- The induced central depth shift is twice the diagonal parameter's value. -/
theorem depthDouble_diagonal_scale (t : Lˣ) (z : Parameters.central c) :
    Parameters.depthDouble omega (Parameters.centralScale (diagonalRootScalar c t : L) z) =
      (omega (t : L) + omega (t : L)) + Parameters.depthDouble omega z := by
  rw [Parameters.depthDouble_centralScale omega hinv, diagonalRootScalar_value omega hinv]

include hinv in
/-- Exact conjugation of the embedded root filtration, including surjectivity. -/
theorem map_conj_diagonal_filtration (t : Lˣ) (s r : ℝ)
    (ht : omega (t : L) = (s : WithTop ℝ)) :
    ((Parameters.filtration omega hinv r).map (Parameters.embedding c)).map
        (MulAut.conj (diagonal c t)).toMonoidHom =
      (Parameters.filtration omega hinv (r + s)).map (Parameters.embedding c) := by
  rw [map_conj_diagonal]
  congr 1
  rw [← Parameters.comap_filtration_scale omega hinv (diagonalRootScalar c t) s r
    ((diagonalRootScalar_value omega hinv t).trans ht)]
  exact Subgroup.map_comap_eq_self_of_surjective
    (Parameters.scaleEquiv (diagonalRootScalar c t)).surjective _

include hinv in
/-- The embedded central filtration is conjugated with twice the level shift. -/
theorem map_conj_diagonal_centralFiltration (t : Lˣ) (s r : ℝ)
    (ht : omega (t : L) = (s : WithTop ℝ)) :
    ((Parameters.centralFiltration omega hinv r).map (Parameters.embedding c)).map
        (MulAut.conj (diagonal c t)).toMonoidHom =
      (Parameters.centralFiltration omega hinv (r + 2 * s)).map (Parameters.embedding c) := by
  rw [map_conj_diagonal]
  congr 1
  rw [← Parameters.comap_centralFiltration_scale omega hinv (diagonalRootScalar c t) s r
    ((diagonalRootScalar_value omega hinv t).trans ht)]
  exact Subgroup.map_comap_eq_self_of_surjective
    (Parameters.scaleEquiv (diagonalRootScalar c t)).surjective _

end Valuation

end Langlands.GroupScheme.SU3Root
