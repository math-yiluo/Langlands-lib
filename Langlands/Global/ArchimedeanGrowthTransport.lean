import Langlands.Global.ArchimedeanGLTransport
import Langlands.Global.ArchimedeanGrowth

/-! # Polynomial growth under actual arithmetic archimedean transport -/

noncomputable section
universe uK uL uM

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGLTransport

open NumberField AdelicFunctoriality ArchimedeanGL

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- An explicit constant bounding arithmetic transport on matrices and their inverses. -/
def growthBound (n : ℕ) (e : K ≃+* L) : ℝ :=
  max 1 ‖(matrixRealLinearEquiv n e).toContinuousLinearMap‖

theorem one_le_growthBound (n : ℕ) (e : K ≃+* L) : 1 ≤ growthBound n e :=
  le_max_left _ _

theorem growthBound_nonneg (n : ℕ) (e : K ≃+* L) : 0 ≤ growthBound n e :=
  le_trans zero_le_one (one_le_growthBound n e)

/-- The existing mixed-coordinate formula, evaluated on the actual infinite matrix group. -/
theorem coordinates_arithmetic_map_apply (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL K n) :
    archimedeanGLCoordinates L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) =
      Matrix.GeneralLinearGroup.map (mixedEquiv e).toRingHom
        (archimedeanGLCoordinates K n g) := by
  simpa only [ContinuousMulEquiv.symm_apply_apply] using
    coordinates_arithmetic_map n e (archimedeanGLCoordinates K n g)

private theorem norm_coordinates_arithmetic_map_le (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL K n) :
    ‖(archimedeanGLCoordinates L n
      (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g)).val‖ ≤
        growthBound n e * matrixHeight K n g := by
  rw [coordinates_arithmetic_map_apply]
  change ‖matrixRealLinearEquiv n e (archimedeanGLCoordinates K n g).val‖ ≤ _
  calc
    _ ≤ ‖(matrixRealLinearEquiv n e).toContinuousLinearMap‖ *
        ‖(archimedeanGLCoordinates K n g).val‖ :=
      (matrixRealLinearEquiv n e).toContinuousLinearMap.le_opNorm _
    _ ≤ growthBound n e * matrixHeight K n g :=
      mul_le_mul (le_max_right _ _) (norm_val_le_matrixHeight K n g)
        (norm_nonneg _) (growthBound_nonneg n e)

/-- Arithmetic transport increases the concrete matrix/inverse height by at most this constant. -/
theorem matrixHeight_arithmetic_map_le (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL K n) :
    matrixHeight L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) ≤
      growthBound n e * matrixHeight K n g := by
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_growthBound n e) (one_le_matrixHeight K n g)
  · apply max_le
    · exact norm_coordinates_arithmetic_map_le n e g
    · have h := norm_coordinates_arithmetic_map_le n e g⁻¹
      rw [map_inv, map_inv, matrixHeight_inv] at h
      exact h

/-- Precomposition retains the exponent and multiplies the constant by `growthBound ^ d`. -/
theorem hasPolynomialGrowth_arithmetic_map (n : ℕ) (e : K ≃+* L)
    {f : InfiniteAdelicGL L n → ℂ} (hf : HasPolynomialGrowth L n f) :
    HasPolynomialGrowth K n (fun g =>
      f (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * growthBound n e ^ d,
    mul_nonneg hC (pow_nonneg (growthBound_nonneg n e) d), d, ?_⟩
  intro g
  calc
    _ ≤ C * matrixHeight L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) ^ d := hf _
    _ ≤ C * (growthBound n e * matrixHeight K n g) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (matrixHeight_nonneg L n _)
          (matrixHeight_arithmetic_map_le n e g) d) hC
    _ = (C * growthBound n e ^ d) * matrixHeight K n g ^ d := by
      rw [mul_pow, mul_assoc]

private theorem arithmetic_map_symm_apply (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL L n) :
    Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e.symm).toRingHom g) = g := by
  have h := infiniteAdeleEquiv_trans e.symm e
  rw [RingEquiv.symm_trans_self, infiniteAdeleEquiv_refl] at h
  have hg := congrArg (fun a : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L =>
    Matrix.GeneralLinearGroup.map a.toRingHom g) h
  exact hg.symm

/-- Polynomial growth for the concrete height is preserved and reflected. -/
theorem hasPolynomialGrowth_arithmetic_map_iff (n : ℕ) (e : K ≃+* L)
    (f : InfiniteAdelicGL L n → ℂ) :
    HasPolynomialGrowth K n (fun g =>
      f (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g)) ↔
        HasPolynomialGrowth L n f := by
  constructor
  · intro hf
    simpa only [arithmetic_map_symm_apply] using
      hasPolynomialGrowth_arithmetic_map n e.symm hf
  · exact hasPolynomialGrowth_arithmetic_map n e

/-- Actual arithmetic pullback on the existing polynomial-growth submodule. -/
def polynomialGrowthComap (n : ℕ) (e : K ≃+* L) :
    polynomialGrowthFunctions L n →ₗ[ℂ] polynomialGrowthFunctions K n where
  toFun f := ⟨fun g => f.val
    (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g),
      hasPolynomialGrowth_arithmetic_map n e f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem polynomialGrowthComap_apply (n : ℕ) (e : K ≃+* L)
    (f : polynomialGrowthFunctions L n) (g : InfiniteAdelicGL K n) :
    (polynomialGrowthComap n e f).val g =
      f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) := rfl

@[simp] theorem polynomialGrowthComap_refl (n : ℕ) (f : polynomialGrowthFunctions K n) :
    polynomialGrowthComap n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  funext g
  change f.val (Matrix.GeneralLinearGroup.map
    (infiniteAdeleEquiv (RingEquiv.refl K)).toRingHom g) = f.val g
  rw [infiniteAdeleEquiv_refl]
  rfl

theorem polynomialGrowthComap_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : polynomialGrowthFunctions M n) :
    polynomialGrowthComap n (e.trans a) f =
      polynomialGrowthComap n e (polynomialGrowthComap n a f) := by
  apply Subtype.ext
  funext g
  change f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv (e.trans a)).toRingHom g) =
    f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv a).toRingHom
      (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g))
  rw [infiniteAdeleEquiv_trans]
  rfl

/-- A genuine complex-linear equivalence on the actual polynomial-growth functions. -/
def polynomialGrowthEquiv (n : ℕ) (e : K ≃+* L) :
    polynomialGrowthFunctions L n ≃ₗ[ℂ] polynomialGrowthFunctions K n where
  __ := polynomialGrowthComap n e
  invFun := polynomialGrowthComap n e.symm
  left_inv f := by
    change polynomialGrowthComap n e.symm (polynomialGrowthComap n e f) = f
    rw [← polynomialGrowthComap_trans]
    simp only [RingEquiv.symm_trans_self, polynomialGrowthComap_refl]
  right_inv f := by
    change polynomialGrowthComap n e (polynomialGrowthComap n e.symm f) = f
    rw [← polynomialGrowthComap_trans]
    simp only [RingEquiv.self_trans_symm, polynomialGrowthComap_refl]

@[simp] theorem polynomialGrowthEquiv_apply (n : ℕ) (e : K ≃+* L)
    (f : polynomialGrowthFunctions L n) (g : InfiniteAdelicGL K n) :
    (polynomialGrowthEquiv n e f).val g =
      f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) := rfl

@[simp] theorem polynomialGrowthEquiv_symm_apply (n : ℕ) (e : K ≃+* L)
    (f : polynomialGrowthFunctions K n) (g : InfiniteAdelicGL L n) :
    ((polynomialGrowthEquiv n e).symm f).val g =
      f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e.symm).toRingHom g) := rfl

/-- The smooth pullback preserves exactly the same growth condition. -/
theorem smoothComap_hasPolynomialGrowth_iff (n : ℕ) (e : K ≃+* L)
    (f : SmoothFunctions L n) :
    HasPolynomialGrowth K n (smoothComap n e f).val ↔
      HasPolynomialGrowth L n f.val :=
  hasPolynomialGrowth_arithmetic_map_iff n e f.val

end Langlands.Global.ArchimedeanGLTransport
