import Langlands.Global.ArchimedeanScalarOrbitDifferentiation
import Langlands.Global.ArchimedeanJointFinite

/-! # Joint finiteness of genuine scalar orbit coefficients -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Scalar orbit formation as an endomorphism of the actual smooth functions. -/
def smoothOrbitCoefficientEnd
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ) :
    SmoothFunctions K n →ₗ[ℂ] SmoothFunctions K n :=
  (smoothOrbitCoefficientLinear K n ℓ).comp
    (DerivativeSmoothFunctions.toSmooth K n).symm.toLinearMap

theorem envelopingAction_smoothOrbitCoefficientEnd
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (a : EnvelopingAlgebra K n) (F : SmoothFunctions K n) :
    envelopingAction K n a (smoothOrbitCoefficientEnd K n ℓ F) =
      smoothOrbitCoefficientEnd K n ℓ (envelopingAction K n a F) := by
  change envelopingAction K n a
      (smoothOrbitCoefficient K n ℓ ((DerivativeSmoothFunctions.toSmooth K n).symm F)) =
    smoothOrbitCoefficient K n ℓ
      ((DerivativeSmoothFunctions.toSmooth K n).symm (envelopingAction K n a F))
  rw [envelopingAction_smoothOrbitCoefficient]
  congr 1

/-- The coefficient map intertwines the genuine joint differential action. -/
def smoothOrbitCoefficientJointIntertwiner
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ) :
    (jointRepresentation K n).IntertwiningMap (jointRepresentation K n) where
  toLinearMap := smoothOrbitCoefficientEnd K n ℓ
  isIntertwining' p := by
    ext F : 1
    change smoothOrbitCoefficientEnd K n ℓ
        (envelopingAction K n (centerInclusion K n p.1 * p.2.val) F) =
      envelopingAction K n (centerInclusion K n p.1 * p.2.val)
        (smoothOrbitCoefficientEnd K n ℓ F)
    exact (envelopingAction_smoothOrbitCoefficientEnd K n ℓ _ F).symm

/-- A finite actual joint orbit stays finite under scalar orbit formation. -/
theorem isJointFinite_smoothOrbitCoefficient
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n)
    (hf : IsJointFinite K n (DerivativeSmoothFunctions.toSmooth K n f)) :
    IsJointFinite K n (smoothOrbitCoefficient K n ℓ f) := by
  have h := Langlands.FiniteVectors.IsFiniteVector.map
    (smoothOrbitCoefficientJointIntertwiner K n ℓ) hf
  change IsJointFinite K n
    (smoothOrbitCoefficient K n ℓ
      ((DerivativeSmoothFunctions.toSmooth K n).symm
        (DerivativeSmoothFunctions.toSmooth K n f))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end Langlands.Global.ArchimedeanGL
