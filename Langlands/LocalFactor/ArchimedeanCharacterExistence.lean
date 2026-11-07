import Langlands.HarmonicAnalysis.ArchimedeanCharacterParameters
import Langlands.LocalFactor.ArchimedeanScaling
import Mathlib.RingTheory.Complex

/-! # Archimedean character presentations -/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open Langlands.HarmonicAnalysis

theorem exists_realScaledCharacter (ψ : UnitaryAdditiveCharacter ℝ) :
    ∃ a : ℝˣ, ∀ x : ℝ, ψ x = realScaledCharacter a x := by
  obtain ⟨c, hc⟩ := exists_circle_exp_mul_of_continuous_add ψ ψ.continuous_toFun
    ψ.toAddChar.map_zero_eq_one ψ.toAddChar.map_add_eq_mul
  have hc0 : c ≠ 0 := by
    intro h
    apply ψ.nontrivial
    ext x
    simp [hc, h]
  let a : ℝˣ := Units.mk0 (c / (2 * Real.pi)) (div_ne_zero hc0 (by positivity))
  refine ⟨a, fun x => ?_⟩
  rw [hc, realScaledCharacter_apply, Real.fourierChar_apply']
  congr 1
  dsimp [a]
  field_simp

theorem exists_complexScaledCharacter (ψ : UnitaryAdditiveCharacter ℂ) :
    ∃ a : ℂˣ, ∀ z : ℂ, ψ z = complexScaledCharacter a z := by
  obtain ⟨c, d, hc⟩ := exists_circle_exp_re_im_of_continuous_add ψ ψ.continuous_toFun
    ψ.toAddChar.map_zero_eq_one ψ.toAddChar.map_add_eq_mul
  let a : ℂ := ⟨c / (4 * Real.pi), -d / (4 * Real.pi)⟩
  have ha (z : ℂ) : ψ z = Real.fourierChar (Algebra.trace ℝ ℂ (a * z)) := by
    rw [hc, Real.fourierChar_apply', Algebra.trace_complex_apply]
    congr 1
    simp only [Complex.mul_re, a]
    field_simp
    ring
  have ha0 : a ≠ 0 := by
    intro h
    apply ψ.nontrivial
    ext z
    simp [ha, h]
  exact ⟨Units.mk0 a ha0, ha⟩

/-- A chosen actual scale for a nontrivial real additive character. -/
def realAdditiveScale (ψ : UnitaryAdditiveCharacter ℝ) : ℝˣ :=
  Classical.choose (exists_realScaledCharacter ψ)

theorem realAdditiveScale_spec (ψ : UnitaryAdditiveCharacter ℝ) (x : ℝ) :
    ψ x = realScaledCharacter (realAdditiveScale ψ) x :=
  Classical.choose_spec (exists_realScaledCharacter ψ) x

/-- A chosen actual trace scale for a nontrivial complex additive character. -/
def complexAdditiveScale (ψ : UnitaryAdditiveCharacter ℂ) : ℂˣ :=
  Classical.choose (exists_complexScaledCharacter ψ)

theorem complexAdditiveScale_spec (ψ : UnitaryAdditiveCharacter ℂ) (z : ℂ) :
    ψ z = complexScaledCharacter (complexAdditiveScale ψ) z :=
  Classical.choose_spec (exists_complexScaledCharacter ψ) z

/-- The positive real exponential, as an actual real unit. -/
def realExponentialUnit (x : ℝ) : ℝˣ where
  val := Real.exp x
  inv := Real.exp (-x)
  val_inv := by rw [← Real.exp_add]; simp
  inv_val := by rw [← Real.exp_add]; simp

@[simp]
theorem coe_realExponentialUnit (x : ℝ) :
    (realExponentialUnit x : ℝ) = Real.exp x := rfl

@[simp]
theorem realExponentialUnit_zero : realExponentialUnit 0 = 1 := by
  apply Units.ext
  simp

theorem realExponentialUnit_add (x y : ℝ) :
    realExponentialUnit (x + y) = realExponentialUnit x * realExponentialUnit y := by
  apply Units.ext
  exact Real.exp_add x y

theorem continuous_realExponentialUnit : Continuous realExponentialUnit :=
  Units.continuous_iff.mpr ⟨Real.continuous_exp, Real.continuous_exp.comp continuous_neg⟩

theorem exists_realCharacterParameters (η : ℝˣ →ₜ* ℂˣ) :
    ∃ (p : Fin 2) (c : ℂ), ∀ x : ℝˣ, (η x : ℂ) =
      (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) ^ p.val * ((|(x : ℝ)| : ℝ) : ℂ) ^ c := by
  obtain ⟨c, hc⟩ := exists_exp_mul_of_continuous_add
    (fun x : ℝ => (η (realExponentialUnit x) : ℂ))
    (Units.continuous_val.comp (η.continuous.comp continuous_realExponentialUnit))
    (by simp)
    (by intro x y; simp [realExponentialUnit_add, map_mul])
    (fun x => (η _).ne_zero)
  have hpos (x : ℝˣ) (hx : 0 < (x : ℝ)) :
      (η x : ℂ) = ((x : ℝ) : ℂ) ^ c := by
    have he : realExponentialUnit (Real.log (x : ℝ)) = x := by
      apply Units.ext
      exact Real.exp_log hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast x.ne_zero),
      ← Complex.ofReal_log hx.le, ← he, hc]
    congr 1
    simp only [coe_realExponentialUnit, Real.exp_log hx]
    ring
  have hsq : (η (-1) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    norm_num
  obtain ⟨p, hp⟩ : ∃ p : Fin 2, (η (-1) : ℂ) = (-1 : ℂ) ^ p.val := by
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  refine ⟨p, c, fun x => ?_⟩
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · have hnx : 0 < ((-x : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hx
    have hdecomp : (-1 : ℝˣ) * (-x) = x := by
      apply Units.ext
      simp
    calc
      (η x : ℂ) = (η (-1) : ℂ) * (η (-x) : ℂ) := by
        rw [← Units.val_mul, ← map_mul, hdecomp]
      _ = (-1 : ℂ) ^ p.val * (((-x : ℝˣ) : ℝ) : ℂ) ^ c := by rw [hp, hpos _ hnx]
      _ = _ := by simp [abs_of_neg hx]
  · simpa [abs_of_pos hx, div_self x.ne_zero] using hpos x hx

/-- Polar data for an arbitrary actual continuous quasicharacter of the real field. -/
def realCharacterData (η : ℝˣ →ₜ* ℂˣ) : RealCharacterData where
  character := η
  parity := Classical.choose (exists_realCharacterParameters η)
  exponent := Classical.choose (Classical.choose_spec (exists_realCharacterParameters η))
  character_eq :=
    Classical.choose_spec (Classical.choose_spec (exists_realCharacterParameters η))

@[simp]
theorem realCharacterData_character (η : ℝˣ →ₜ* ℂˣ) :
    (realCharacterData η).character = η := rfl

end Langlands.LocalFactor.Archimedean
