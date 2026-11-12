import Langlands.Global.HeckeNormTwist

/-! # Complex powers of the idelic norm as Hecke characters -/

noncomputable section
universe u

namespace Langlands.Global

open scoped WithZero NNReal

variable (F : Type u) [Field F] [NumberField F]

namespace HeckeCharacter

/-- The complex-valued power `a ↦ exp (s log |a|)` of the actual idelic norm. -/
def normPowerValue (s : ℂ) : IdeleClasses F →* ℂ where
  toFun a := Complex.exp
    (s * ((Real.log ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) : ℝ) : ℂ))
  map_one' := by simp
  map_mul' a b := by
    have ha : ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (IdeleAbsoluteValue.ideleClass F a).ne_zero
    have hb : ((IdeleAbsoluteValue.ideleClass F b : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (IdeleAbsoluteValue.ideleClass F b).ne_zero
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul ha hb,
      Complex.ofReal_add, mul_add, Complex.exp_add]

theorem continuous_normPowerValue (s : ℂ) :
    Continuous (normPowerValue F s) := by
  have hc : Continuous fun a : IdeleClasses F =>
      ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) := by fun_prop
  have hl := hc.log (fun a => by
    exact_mod_cast (IdeleAbsoluteValue.ideleClass F a).ne_zero)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hl))

/-- The Hecke character `‖·‖^s : a ↦ |a|^s = exp (s log |a|)`, for a complex
exponent `s`, with the normalized idelic norm `IdeleAbsoluteValue.ideleClass`. -/
def normPower (s : ℂ) : HeckeCharacter F where
  toMonoidHom := (normPowerValue F s).toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_normPowerValue F s,
      (continuous_normPowerValue F s).comp continuous_inv⟩

@[simp] theorem normPower_apply (s : ℂ) (a : IdeleClasses F) :
    (normPower F s a : ℂ) = Complex.exp
      (s * ((Real.log ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) : ℝ) : ℂ)) :=
  rfl

/-- For a real exponent, `normPower` is the real power of the idelic norm. -/
theorem normPower_ofReal_apply (s : ℝ) (a : IdeleClasses F) :
    (normPower F s a : ℂ) =
      ((((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) ^ s : ℝ) : ℂ) := by
  have hpos : 0 < ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) := by
    have h := (IdeleAbsoluteValue.ideleClass F a).ne_zero
    positivity
  rw [normPower_apply, Real.rpow_def_of_pos hpos, Complex.ofReal_exp]
  push_cast
  ring_nf

@[simp] theorem normPower_zero : normPower F 0 = 1 := by
  ext a
  simp

theorem normPower_add (s t : ℂ) :
    normPower F (s + t) = normPower F s * normPower F t := by
  ext a
  simp [add_mul, Complex.exp_add]

/-- The published imaginary powers are the special case `s = i t`. -/
theorem unitaryNormPower_eq_normPower (t : ℝ) :
    unitaryNormPower F t = normPower F ((t : ℂ) * Complex.I) := by
  ext a
  simp only [unitaryNormPower_apply, normPower_apply]
  push_cast
  ring_nf

@[simp] theorem normPower_finiteComponent (s : ℂ) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) :
    ((normPower F s).finiteComponent v a : ℂ) =
      Complex.exp (s * ((Real.log ‖a.val‖ : ℝ) : ℂ)) := by
  change Complex.exp
    (s * ((Real.log ((IdeleAbsoluteValue.ideleClass F
      (finiteClassInclusion F v a) : ℝ≥0) : ℝ) : ℝ) : ℂ)) = _
  rw [IdeleAbsoluteValue.coe_ideleClass_finiteClassInclusion]

/-- Every complex power of the norm is unramified at every finite place. -/
theorem normPower_isUnramifiedAt (s : ℂ) (v : FinitePlace F) :
    (normPower F s).IsUnramifiedAt v := by
  intro a ha
  have hv : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) a.val = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v) (a := a)).mp ha
  have hn : ‖a.val‖ = 1 :=
    (Valued.toNormedField.norm_eq_one_iff (Γ₀ := ℤᵐ⁰)).mpr hv
  apply Units.ext
  simp [hn]

end HeckeCharacter
end Langlands.Global
