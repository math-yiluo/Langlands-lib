import Langlands.Global.HeckeCharacter
import Langlands.Global.IdeleAbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Unitary norm powers and unramified local character prescription -/

noncomputable section
universe u

namespace Langlands.Global

open scoped WithZero NNReal

variable (F : Type u) [Field F] [NumberField F]

namespace HeckeCharacter

/-- The complex-valued imaginary power of the actual idelic norm. -/
def unitaryNormPowerValue (t : ℝ) : IdeleClasses F →* ℂ where
  toFun a := Complex.exp
    (((t * Real.log ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ)) : ℝ) * Complex.I)
  map_one' := by simp
  map_mul' a b := by
    have ha : ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (IdeleAbsoluteValue.ideleClass F a).ne_zero
    have hb : ((IdeleAbsoluteValue.ideleClass F b : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (IdeleAbsoluteValue.ideleClass F b).ne_zero
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul ha hb,
      mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem continuous_unitaryNormPowerValue (t : ℝ) :
    Continuous (unitaryNormPowerValue F t) := by
  have hc : Continuous fun a : IdeleClasses F =>
      ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ) := by fun_prop
  have hl := hc.log (fun a => by
    exact_mod_cast (IdeleAbsoluteValue.ideleClass F a).ne_zero)
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul hl)).mul_const Complex.I)

/-- A unitary Hecke character `a ↦ exp(i t log |a|)`. -/
def unitaryNormPower (t : ℝ) : HeckeCharacter F where
  toMonoidHom := (unitaryNormPowerValue F t).toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_unitaryNormPowerValue F t,
      (continuous_unitaryNormPowerValue F t).comp continuous_inv⟩

@[simp] theorem unitaryNormPower_apply (t : ℝ) (a : IdeleClasses F) :
    (unitaryNormPower F t a : ℂ) = Complex.exp
      (((t * Real.log ((IdeleAbsoluteValue.ideleClass F a : ℝ≥0) : ℝ)) : ℝ) * Complex.I) :=
  rfl

theorem unitaryNormPower_isUnitary (t : ℝ) :
    (unitaryNormPower F t).IsUnitary := by
  intro a
  simp [Complex.norm_exp]

@[simp] theorem unitaryNormPower_finiteComponent (t : ℝ) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) :
    ((unitaryNormPower F t).finiteComponent v a : ℂ) =
      Complex.exp (((t * Real.log ‖a.val‖) : ℝ) * Complex.I) := by
  change Complex.exp
    (((t * Real.log ((IdeleAbsoluteValue.ideleClass F
      (finiteClassInclusion F v a) : ℝ≥0) : ℝ)) : ℝ) * Complex.I) = _
  rw [IdeleAbsoluteValue.coe_ideleClass_finiteClassInclusion]

theorem unitaryNormPower_isUnramifiedAt (t : ℝ) (v : FinitePlace F) :
    (unitaryNormPower F t).IsUnramifiedAt v := by
  intro a ha
  have hv : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) a.val = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v) (a := a)).mp ha
  have hn : ‖a.val‖ = 1 :=
    (Valued.toNormedField.norm_eq_one_iff (Γ₀ := ℤᵐ⁰)).mpr hv
  apply Units.ext
  simp [hn]

variable {F}

/-- Unramified characters of a finite completion are determined by their value
on any element of valuation exponent one. -/
theorem finiteComponent_ext_of_generator (v : FinitePlace F)
    (χ ψ : (FiniteCompletion F v)ˣ →ₜ* ℂˣ)
    (hχ : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → χ a = 1)
    (hψ : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → ψ a = 1)
    (b : (FiniteCompletion F v)ˣ)
    (hb : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) b.val =
      WithZero.exp (1 : ℤ))
    (h : χ b = ψ b) : χ = ψ := by
  apply ContinuousMonoidHom.ext
  intro a
  let ν : Valuation (FiniteCompletion F v) ℤᵐ⁰ := Valued.v
  have ha0 : ν a.val ≠ 0 := ν.ne_zero_iff.mpr a.ne_zero
  let n : ℤ := WithZero.log (ν a.val)
  have hbn : ν ((b ^ n).val) = ν a.val := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hb]
    simpa only [← WithZero.exp_zsmul, Int.zsmul_eq_mul, mul_one, n] using
      (WithZero.exp_log ha0)
  have hu : (a / b ^ n) ∈
      (Submonoid.ofClass (v.adicCompletionIntegers F)).units := by
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v) (a := a / b ^ n)).mpr
    rw [Units.val_div_eq_div_val]
    change ν (a.val / (b ^ n).val) = 1
    rw [map_div₀, hbn, div_self ha0]
  calc
    χ a = χ (b ^ n) := div_eq_one.mp (by simpa using hχ (a / b ^ n) hu)
    _ = ψ (b ^ n) := by simp only [map_zpow, h]
    _ = ψ a := (div_eq_one.mp (by simpa using hψ (a / b ^ n) hu)).symm

/-- Every unitary unramified character at one finite place is the component of
an imaginary power of the global idelic norm. -/
theorem exists_unitaryNormPower_finiteComponent (v : FinitePlace F)
    (η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ)
    (hη : ∀ a, ‖(η a : ℂ)‖ = 1)
    (hηU : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → η a = 1) :
    ∃ t : ℝ, (unitaryNormPower F t).finiteComponent v = η := by
  obtain ⟨b, hb⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
      (WithZero.exp (1 : ℤ))
  have hb0 : b ≠ 0 := by
    intro h
    exact (WithZero.exp_ne_zero (a := (1 : ℤ)))
      (by simpa only [h, map_zero] using hb.symm)
  let bU : (FiniteCompletion F v)ˣ := Units.mk0 b hb0
  have hbn : 1 < ‖b‖ := by
    apply (Valued.toNormedField.one_lt_norm_iff (Γ₀ := ℤᵐ⁰)).mpr
    rw [hb]
    exact (WithZero.exp_lt_exp).mpr (show (0 : ℤ) < 1 by decide)
  have hlog : Real.log ‖b‖ ≠ 0 := ne_of_gt (Real.log_pos hbn)
  let t : ℝ := Complex.arg (η bU) / Real.log ‖b‖
  refine ⟨t, finiteComponent_ext_of_generator v _ η
    (unitaryNormPower_isUnramifiedAt F t v) hηU bU hb ?_⟩
  apply Units.ext
  rw [unitaryNormPower_finiteComponent]
  change Complex.exp (((Complex.arg (η bU) / Real.log ‖b‖ * Real.log ‖b‖) : ℝ) *
    Complex.I) = (η bU : ℂ)
  rw [div_mul_cancel₀ _ hlog]
  simpa only [hη bU, Complex.ofReal_one, one_mul] using
    Complex.norm_mul_exp_arg_mul_I (η bU)

/-- A unitary unramified local character extends globally, with every finite
component unramified. -/
theorem exists_unitary_unramified_extension (v : FinitePlace F)
    (η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ)
    (hη : ∀ a, ‖(η a : ℂ)‖ = 1)
    (hηU : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → η a = 1) :
    ∃ χ : HeckeCharacter F, χ.IsUnitary ∧
      (∀ w, χ.IsUnramifiedAt w) ∧ χ.finiteComponent v = η := by
  obtain ⟨t, ht⟩ := exists_unitaryNormPower_finiteComponent v η hη hηU
  exact ⟨unitaryNormPower F t, unitaryNormPower_isUnitary F t,
    unitaryNormPower_isUnramifiedAt F t, ht⟩

end HeckeCharacter
end Langlands.Global
