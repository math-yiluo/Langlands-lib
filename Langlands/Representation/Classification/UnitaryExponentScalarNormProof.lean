import Langlands.Representation.Classification.UnitaryExponentScalarNormStatement

/-!
# Scalar norms from arbitrary unitary exponent data

The supplied negative-twist invariant form forces a scalar operator to have
norm equal to the positive-character power specified by its exponent.
-/

open scoped NNReal

namespace Langlands

/-- Extract a scalar's norm using the form of the supplied unitary exponent
witness, on an arbitrary nontrivial complex vector space. -/
theorem unitaryExponentScalarNorm.{uG, uV} :
    UnitaryExponentScalarNorm.{uG, uV} := by
  intro G _ V _ _ _ ν ρ u g c hc
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let : InnerProductSpace.Core ℂ V := u.form.toInnerProductCore
  let : Inner ℂ V := u.form.toInnerProductCore.toInner
  let a : ℝ := ((ν g : ℝ≥0) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (pos_iff_ne_zero.mpr (ν g).ne_zero)
  let k : ℂ := (a ^ (-u.exponent) : ℝ) * c
  have hact : realPowerTwist ν (-u.exponent) ρ g v = k • v := by
    rw [realPowerTwist_apply, hc, smul_smul]
  have hdiag : inner ℂ v v ≠ 0 := fun h => hv (u.form.definite v h)
  have hinv := u.form.invariant g v v
  rw [hact] at hinv
  change inner ℂ (k • v) (k • v) = inner ℂ v v at hinv
  rw [InnerProductSpace.Core.inner_smul_left,
    InnerProductSpace.Core.inner_smul_right] at hinv
  have hunit : (starRingEnd ℂ) k * k = 1 := by
    apply mul_right_cancel₀ hdiag
    simpa only [mul_assoc, one_mul] using hinv
  have hnormmul : ‖k‖ * ‖k‖ = 1 := by
    simpa only [norm_mul, Complex.norm_conj, norm_one] using
      congrArg (fun z : ℂ => ‖z‖) hunit
  have hnorm : ‖k‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg k) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [pow_two, one_mul] using hnormmul
  have hfactor : a ^ (-u.exponent) * ‖c‖ = 1 := by
    simpa only [k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ha (-u.exponent))] using hnorm
  rw [Real.rpow_neg ha.le] at hfactor
  have hp : a ^ u.exponent ≠ 0 := (Real.rpow_pos_of_pos ha u.exponent).ne'
  change ‖c‖ = a ^ u.exponent
  calc
    ‖c‖ = a ^ u.exponent * ((a ^ u.exponent)⁻¹ * ‖c‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    _ = a ^ u.exponent := by rw [hfactor, mul_one]

end Langlands
