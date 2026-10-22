import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Canonical inverse half of a positive character

A character with values in the units of the nonnegative reals has strictly
positive values. The square root is canonical. Identifying the input with a
particular group's modulus is an obligation of each geometric application.
-/

namespace Langlands.Jacquet

open scoped NNReal

universe uH

variable {H : Type uH} [Group H]

/-- Embed a positive character into the complex units. -/
def complexCharacter (δ : H →* ℝ≥0ˣ) : H →* ℂˣ :=
  (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp δ

@[simp]
theorem complexCharacter_apply (δ : H →* ℝ≥0ˣ) (h : H) :
    (complexCharacter δ h : ℂ) = (((δ h : ℝ≥0) : ℝ) : ℂ) := rfl

/-- The canonical positive square root of a positive character. -/
noncomputable def positiveHalfCharacter (δ : H →* ℝ≥0ˣ) : H →* ℝ≥0ˣ :=
  (Units.map NNReal.sqrtHom.toMonoidHom).comp δ

@[simp]
theorem positiveHalfCharacter_apply (δ : H →* ℝ≥0ˣ) (h : H) :
    (positiveHalfCharacter δ h : ℝ≥0) = NNReal.sqrt (δ h : ℝ≥0) := rfl

/-- The inverse, rather than the positive half, used for Jacquet normalization. -/
noncomputable def inverseHalfCharacter (δ : H →* ℝ≥0ˣ) : H →* ℂˣ :=
  (complexCharacter (positiveHalfCharacter δ))⁻¹

@[simp]
theorem inverseHalfCharacter_apply (δ : H →* ℝ≥0ˣ) (h : H) :
    (inverseHalfCharacter δ h : ℂ) =
      (((NNReal.sqrt (δ h : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
  simp [inverseHalfCharacter]

theorem positiveHalfCharacter_sq (δ : H →* ℝ≥0ˣ) (h : H) :
    positiveHalfCharacter δ h ^ 2 = δ h := by
  apply Units.ext
  simp

/-- This identity records the direction and magnitude of normalization. -/
theorem inverseHalfCharacter_sq (δ : H →* ℝ≥0ˣ) (h : H) :
    inverseHalfCharacter δ h ^ 2 = (complexCharacter δ h)⁻¹ := by
  change (complexCharacter (positiveHalfCharacter δ) h)⁻¹ ^ 2 = _
  rw [inv_pow]
  congr 1
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, complexCharacter_apply, positiveHalfCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

@[simp]
theorem inverseHalfCharacter_eq_one (δ : H →* ℝ≥0ˣ) (h : H) :
    inverseHalfCharacter δ h = 1 ↔ δ h = 1 := by
  rw [Units.ext_iff, Units.ext_iff]
  simp

theorem inverseHalfCharacter_ker (δ : H →* ℝ≥0ˣ) :
    (inverseHalfCharacter δ).ker = δ.ker := by
  ext h
  exact inverseHalfCharacter_eq_one δ h

/-- An open-kernel positive modulus gives an open-kernel inverse half character. -/
theorem isOpen_ker_inverseHalfCharacter [TopologicalSpace H] (δ : H →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set H)) :
    IsOpen ((inverseHalfCharacter δ).ker : Set H) := by
  simpa only [inverseHalfCharacter_ker] using hδ

end Langlands.Jacquet
