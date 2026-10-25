import Langlands.Automorphic.RealDifferentialCovarianceStatement
import Langlands.Global.ArchimedeanAdjoint

/-! # Proof of right-translation covariance of actual real differentiation -/

noncomputable section
universe u
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The ambient chain rule for the linear right multiplication `h ↦ h * a`. -/
theorem fderiv_comp_mul_right (f : ArchimedeanMatrix K n → ℂ)
    (a g v : ArchimedeanMatrix K n) (hf : DifferentiableAt ℝ f (g * a)) :
    fderiv ℝ (fun h => f (h * a)) g v = fderiv ℝ f (g * a) (v * a) := by
  have ha : DifferentiableAt ℝ (fun h : ArchimedeanMatrix K n => h * a) g :=
    differentiableAt_id.mul_const a
  rw [fderiv_fun_comp g hf ha]
  change fderiv ℝ f (g * a)
      (fderiv ℝ ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip a) g v) = _
  simp [ContinuousLinearMap.fderiv]

/-- Right translation by `g` carries `D(X)` to `D(g X g⁻¹)`:
`R(g) (D(X) f) = D(Ad(g) X) (R(g) f)` on actual smooth functions. -/
theorem smoothRightAction_smoothDifferential
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (X : RealLieAlgebra K n) (f : SmoothFunctions K n) :
    smoothRightAction K n g (smoothDifferential K n X f) =
      smoothDifferential K n
        ((realLieAlgebraToMatrix K n).symm
          ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
            realLieAlgebraToMatrix K n X *
            (archimedeanGLCoordinates K n g⁻¹ : ArchimedeanMatrix K n)))
        (smoothRightAction K n g f) := by
  apply Subtype.ext
  funext x
  change (smoothDifferential K n X f).val (x * g) =
    (smoothDifferential K n _ (smoothRightAction K n g f)).val x
  have hext (h : ArchimedeanGL K n) :
      coordinateExtension K n f
        ((h : ArchimedeanMatrix K n) *
          (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)) =
        (smoothRightAction K n g f).val ((archimedeanGLCoordinates K n).symm h) := by
    change coordinateExtension K n f
      ((h * archimedeanGLCoordinates K n g : ArchimedeanGL K n) : ArchimedeanMatrix K n) = _
    simp only [coordinateExtension_apply, smoothRightAction_apply, map_mul,
      ContinuousMulEquiv.symm_apply_apply]
  have hdiff : DifferentiableAt ℝ (coordinateExtension K n f)
      ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
        (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)) := by
    simpa only [map_mul, Units.val_mul] using
      (coordinateExtension_contDiffAt K n f
        (archimedeanGLCoordinates K n (x * g))).differentiableAt (by simp)
  rw [smoothDifferential_eq_of_extension K n _ (smoothRightAction K n g f)
      (fun h => coordinateExtension K n f
        (h * (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))) hext,
    fderiv_comp_mul_right K n _ _ _ _ hdiff, LinearEquiv.apply_symm_apply,
    smoothDifferential_apply, map_mul (archimedeanGLCoordinates K n) x g, Units.val_mul,
    map_inv (archimedeanGLCoordinates K n) g]
  congr 1
  simp only [mul_assoc, Units.inv_mul, mul_one]

/-- The same covariance with the published adjoint conjugation `realLieConjugation`. -/
theorem smoothRightAction_smoothDifferential_realLieConjugation
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (X : RealLieAlgebra K n) (f : SmoothFunctions K n) :
    smoothRightAction K n g (smoothDifferential K n X f) =
      smoothDifferential K n (realLieConjugation K n g X) (smoothRightAction K n g f) := by
  rw [realLieConjugation_apply]
  exact smoothRightAction_smoothDifferential K n g X f

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Infinite right translation acts on each actual infinite slice by smooth right
translation. -/
theorem finiteSmoothSlice_ofInfinite_rightAction (g : InfiniteAdelicGL K n)
    (b : FiniteAdelicGL K n) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothSlice K n b (finiteSmoothRightAction K n (AdelicGL.ofInfinite K n g) f) =
      ArchimedeanGL.smoothRightAction K n g (finiteSmoothSlice K n b f) := by
  apply Subtype.ext
  funext a
  change evaluate K n f.val (AdelicGL.pair K n a b * AdelicGL.ofInfinite K n g) =
    evaluate K n f.val (AdelicGL.pair K n (a * g) b)
  rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

/-- The smooth component of the covariance target. -/
theorem smoothRealDifferentialCovariance : SmoothRealDifferentialCovarianceStatement K n :=
  fun g X f => ArchimedeanGL.smoothRightAction_smoothDifferential K n g X f

/-- The finite-smooth component, descended through the faithful infinite slices. -/
theorem finiteSmoothRealDifferentialCovariance :
    FiniteSmoothRealDifferentialCovarianceStatement K n := by
  intro g X f
  apply finiteSmoothSlice_injective K n
  funext b
  dsimp only
  rw [finiteSmoothSlice_ofInfinite_rightAction, finiteSmoothSlice_envelopingAction,
    finiteSmoothSlice_envelopingAction, finiteSmoothSlice_ofInfinite_rightAction,
    ArchimedeanGL.envelopingAction_real_generator,
    ArchimedeanGL.envelopingAction_real_generator]
  exact ArchimedeanGL.smoothRightAction_smoothDifferential K n g X _

/-- Actual smooth and finite-smooth real differential covariance. -/
theorem realDifferentialCovariance : RealDifferentialCovarianceStatement K n :=
  ⟨smoothRealDifferentialCovariance K n, finiteSmoothRealDifferentialCovariance K n⟩

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    RealDifferentialCovarianceStatement K n :=
  @realDifferentialCovariance

end Langlands.Automorphic
