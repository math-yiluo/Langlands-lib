import Langlands.LocalFactor.ArchimedeanCharacterExistence

/-! # Polar parameters of actual complex quasicharacters -/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open Langlands.HarmonicAnalysis

/-- The positive real exponential, embedded as an actual complex unit. -/
def complexExponentialUnit (x : ℝ) : ℂˣ :=
  Units.map Complex.ofRealHom.toMonoidHom (realExponentialUnit x)

@[simp]
theorem coe_complexExponentialUnit (x : ℝ) :
    (complexExponentialUnit x : ℂ) = (Real.exp x : ℂ) := rfl

@[simp]
theorem complexExponentialUnit_zero : complexExponentialUnit 0 = 1 := by
  simp [complexExponentialUnit]

theorem complexExponentialUnit_add (x y : ℝ) :
    complexExponentialUnit (x + y) = complexExponentialUnit x * complexExponentialUnit y := by
  simp [complexExponentialUnit, realExponentialUnit_add]

theorem continuous_complexExponentialUnit : Continuous complexExponentialUnit :=
  Units.continuous_iff.mpr
    ⟨Complex.continuous_ofReal.comp Real.continuous_exp,
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)⟩

theorem exists_complexCharacterParameters (η : ℂˣ →ₜ* ℂˣ) :
    ∃ (n : ℤ) (c : ℂ), ∀ z : ℂˣ, (η z : ℂ) =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n * (‖(z : ℂ)‖ : ℂ) ^ (2 * c) := by
  obtain ⟨c, hc⟩ := exists_exp_mul_of_continuous_add
    (fun x : ℝ => (η (complexExponentialUnit x) : ℂ))
    (Units.continuous_val.comp (η.continuous.comp continuous_complexExponentialUnit))
    (by simp)
    (by intro x y; simp [complexExponentialUnit_add, map_mul])
    (fun x => (η _).ne_zero)
  have hcircle : Continuous Circle.toUnits := by
    apply Continuous.of_coeHom_comp
    exact continuous_subtype_val
  obtain ⟨n, hn⟩ := exists_zpow_of_continuous_circle_mul
    (fun z : Circle => (η (Circle.toUnits z) : ℂ))
    (Units.continuous_val.comp (η.continuous.comp hcircle))
    (by simp)
    (by intro x y; simp [map_mul])
    (fun z => (η _).ne_zero)
  refine ⟨n, c / 2, fun z => ?_⟩
  have hr : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hr0 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    simp⟩
  have hdecomp : Circle.toUnits u * complexExponentialUnit (Real.log ‖(z : ℂ)‖) = z := by
    apply Units.ext
    change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (Real.exp (Real.log ‖(z : ℂ)‖) : ℂ) = (z : ℂ)
    rw [Real.exp_log hr]
    exact div_mul_cancel₀ _ hr0
  have hrad : Complex.exp (c * (Real.log ‖(z : ℂ)‖ : ℂ)) =
      (‖(z : ℂ)‖ : ℂ) ^ (2 * (c / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
    congr 1
    ring
  calc
    (η z : ℂ) = (η (Circle.toUnits u) : ℂ) *
        (η (complexExponentialUnit (Real.log ‖(z : ℂ)‖)) : ℂ) := by
      rw [← Units.val_mul, ← map_mul, hdecomp]
    _ = (u : ℂ) ^ n * Complex.exp (c * (Real.log ‖(z : ℂ)‖ : ℂ)) := by rw [hn, hc]
    _ = _ := by rw [hrad]

/-- Polar data for an arbitrary actual continuous quasicharacter of the complex field. -/
def complexCharacterData (η : ℂˣ →ₜ* ℂˣ) : ComplexCharacterData where
  character := η
  weight := Classical.choose (exists_complexCharacterParameters η)
  exponent := Classical.choose (Classical.choose_spec (exists_complexCharacterParameters η))
  character_eq :=
    Classical.choose_spec (Classical.choose_spec (exists_complexCharacterParameters η))

@[simp]
theorem complexCharacterData_character (η : ℂˣ →ₜ* ℂˣ) :
    (complexCharacterData η).character = η := rfl

end Langlands.LocalFactor.Archimedean
