import Langlands.Global.ArchimedeanCasimirCartan
import Langlands.Global.ArchimedeanEnvelopingAction
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # The concrete Cartan matrix frame and quadratic differential symbol -/

noncomputable section
universe u
open scoped Classical ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Left multiplication by the actual unit gives the left matrix frame. -/
def leftMatrixFrame (g : ArchimedeanGL K n) :
    RealLieAlgebra K n ≃ₗ[ℝ] ArchimedeanMatrix K n where
  toFun X := (g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X
  invFun Y := (realLieAlgebraToMatrix K n).symm
    (((g⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n) * Y)
  left_inv X := by
    simp only [Units.inv_mul_cancel_left, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    simp only [LinearEquiv.apply_symm_apply, Units.mul_inv_cancel_left]
  map_add' X Y := by simp only [map_add, mul_add]
  map_smul' c X := by simp only [map_smul, mul_smul_comm, RingHom.id_apply]

omit [NumberField K] in
@[simp]
theorem leftMatrixFrame_apply (g : ArchimedeanGL K n) (X : RealLieAlgebra K n) :
    leftMatrixFrame K n g X =
      (g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X := rfl

omit [NumberField K] in
@[simp]
theorem leftMatrixFrame_symm_apply (g : ArchimedeanGL K n) (Y : ArchimedeanMatrix K n) :
    (leftMatrixFrame K n g).symm Y = (realLieAlgebraToMatrix K n).symm
      (((g⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n) * Y) := rfl

/-- The normalized Cartan basis transported to the actual ambient matrix tangent space. -/
def leftCartanMatrixBasis (g : ArchimedeanGL K n) :
    Module.Basis (CartanBasisIndex K n) ℝ (ArchimedeanMatrix K n) :=
  (cartanAdaptedBasis K n).map (leftMatrixFrame K n g)

@[simp]
theorem leftCartanMatrixBasis_apply (g : ArchimedeanGL K n) (i : CartanBasisIndex K n) :
    leftCartanMatrixBasis K n g i =
      (g : ArchimedeanMatrix K n) *
        realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i) := rfl

/-- The real second-order covector form, as a sum of squares in the actual left frame. -/
def cartanCovectorForm (g : ArchimedeanGL K n) :
    QuadraticForm ℝ (Module.Dual ℝ (ArchimedeanMatrix K n)) :=
  ∑ i : CartanBasisIndex K n,
    (QuadraticMap.sq (R := ℝ) (A := ℝ)).comp
      (LinearMap.applyₗ (R := ℝ) (M₂ := ℝ) (leftCartanMatrixBasis K n g i))

theorem cartanCovectorForm_apply (g : ArchimedeanGL K n)
    (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)) :
    cartanCovectorForm K n g ℓ = ∑ i : CartanBasisIndex K n,
      (ℓ ((g : ArchimedeanMatrix K n) *
        realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))) ^ 2 := by
  simp [cartanCovectorForm, pow_two]

theorem cartanCovectorForm_nonneg (g : ArchimedeanGL K n)
    (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)) :
    0 ≤ cartanCovectorForm K n g ℓ := by
  rw [cartanCovectorForm_apply]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem cartanCovectorForm_eq_zero_iff (g : ArchimedeanGL K n)
    (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)) :
    cartanCovectorForm K n g ℓ = 0 ↔ ℓ = 0 := by
  constructor
  · intro h
    rw [cartanCovectorForm_apply] at h
    have hz (i : CartanBasisIndex K n) : ℓ (leftCartanMatrixBasis K n g i) = 0 := by
      exact sq_eq_zero_iff.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h i
          (Finset.mem_univ i))
    apply (leftCartanMatrixBasis K n g).ext
    intro i
    simpa only [LinearMap.zero_apply] using hz i
  · rintro rfl
    simp [cartanCovectorForm_apply]

theorem cartanCovectorForm_pos (g : ArchimedeanGL K n)
    (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)) (hℓ : ℓ ≠ 0) :
    0 < cartanCovectorForm K n g ℓ :=
  lt_of_le_of_ne (cartanCovectorForm_nonneg K n g ℓ)
    (Ne.symm ((cartanCovectorForm_eq_zero_iff K n g ℓ).not.mpr hℓ))

/-- Evaluation of the actual second-order coefficient on a real bilinear map. -/
def cartanSecondOrderCoefficient (g : ArchimedeanGL K n)
    (B : ArchimedeanMatrix K n →ₗ[ℝ] ArchimedeanMatrix K n →ₗ[ℝ] ℝ) : ℝ :=
  ∑ i : CartanBasisIndex K n,
    B (leftCartanMatrixBasis K n g i) (leftCartanMatrixBasis K n g i)

/-- Repeated covector evaluation in the second-order coefficient is exactly the quadratic form. -/
theorem cartanCovectorForm_eq_secondOrderCoefficient (g : ArchimedeanGL K n)
    (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)) :
    cartanCovectorForm K n g ℓ =
      cartanSecondOrderCoefficient K n g ((LinearMap.mul ℝ ℝ).compl₁₂ ℓ ℓ) := by
  simp only [cartanCovectorForm_apply, cartanSecondOrderCoefficient, leftCartanMatrixBasis_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', pow_two]

/-- Exact second-order formula for two genuine left matrix directional derivatives. -/
theorem smoothDifferential_iterated_apply (X Y : RealLieAlgebra K n)
    (f : SmoothFunctions K n)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (smoothDifferential K n X (smoothDifferential K n Y f)).val x =
      fderiv ℝ (fderiv ℝ (coordinateExtension K n f))
        (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n Y) +
      fderiv ℝ (coordinateExtension K n f)
        (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y)) := by
  have hext (h : ArchimedeanGL K n) :
      fderiv ℝ (coordinateExtension K n f) (h : ArchimedeanMatrix K n)
          ((h : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Y) =
        (smoothDifferential K n Y f).val ((archimedeanGLCoordinates K n).symm h) := by
    simp only [smoothDifferential_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [smoothDifferential_eq_of_extension K n X (smoothDifferential K n Y f)
    (fun h => fderiv ℝ (coordinateExtension K n f) h
      (h * realLieAlgebraToMatrix K n Y)) hext]
  have hc := ((coordinateExtension_contDiffAt K n f (archimedeanGLCoordinates K n x)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have hu : DifferentiableAt ℝ
      (fun h : ArchimedeanMatrix K n => h * realLieAlgebraToMatrix K n Y)
      (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) :=
    differentiableAt_id.mul_const _
  rw [fderiv_clm_apply hc hu]
  have hright :
      fderiv ℝ (fun h : ArchimedeanMatrix K n => h * realLieAlgebraToMatrix K n Y)
        (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) =
      (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
        (realLieAlgebraToMatrix K n Y) := by
    exact ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
      (realLieAlgebraToMatrix K n Y)).fderiv
  simp only [hright, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_assoc, add_comm]

/-- The genuine full square sum acts as the finite sum of iterated real differentials. -/
theorem envelopingAction_cartanSquareSum (f : SmoothFunctions K n) :
    envelopingAction K n (cartanSquareSum K n) f =
      ∑ i : CartanBasisIndex K n, smoothDifferential K n (cartanAdaptedBasis K n i)
        (smoothDifferential K n (cartanAdaptedBasis K n i) f) := by
  change envelopingAction K n
      (∑ i : CartanBasisIndex K n,
        envelopingGenerator K n (complexify K n (cartanAdaptedBasis K n i)) *
          envelopingGenerator K n (complexify K n (cartanAdaptedBasis K n i))) f = _
  simp only [map_sum, map_mul, envelopingAction_real_generator,
    LinearMap.sum_apply, Module.End.mul_apply]

/-- Every second-order coefficient and the first-order correction of the actual square sum. -/
theorem envelopingAction_cartanSquareSum_apply (f : SmoothFunctions K n)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (envelopingAction K n (cartanSquareSum K n) f).val x =
      ∑ i : CartanBasisIndex K n,
        (fderiv ℝ (fderiv ℝ (coordinateExtension K n f))
          (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
          ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
            realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))
          ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
            realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)) +
        fderiv ℝ (coordinateExtension K n f)
          (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
          ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
            (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i) *
              realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)))) := by
  rw [envelopingAction_cartanSquareSum]
  simp only [Submodule.coe_sum, Finset.sum_apply, smoothDifferential_iterated_apply]

example : ∀ (K : Type u) [Field K] (n : ℕ)
    (g : ArchimedeanGL K n) (X : RealLieAlgebra K n),
    leftMatrixFrame K n g X =
      (g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X :=
  @leftMatrixFrame_apply

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (g : ArchimedeanGL K n) (ℓ : Module.Dual ℝ (ArchimedeanMatrix K n)),
    cartanCovectorForm K n g ℓ = 0 ↔ ℓ = 0 :=
  @cartanCovectorForm_eq_zero_iff

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (X Y : RealLieAlgebra K n) (f : SmoothFunctions K n)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
    (smoothDifferential K n X (smoothDifferential K n Y f)).val x =
      fderiv ℝ (fderiv ℝ (coordinateExtension K n f))
        (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n Y) +
      fderiv ℝ (coordinateExtension K n f)
        (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y)) :=
  @smoothDifferential_iterated_apply

end Langlands.Global.ArchimedeanGL
