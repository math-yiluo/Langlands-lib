import Langlands.Representation.RankinSelberg.TwoBlockDominantNumeratorExtraction
import Langlands.Representation.RankinSelberg.TwoBlockDominantRationalNumerators
import Langlands.Representation.RankinSelberg.PairFactors

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open HarmonicAnalysis LaurentPolynomial LocalFactor

/-- The rational image of the Laurent monomial is the epsilon monomial. -/
theorem laurentToRatFunc_epsilon (c : ℂˣ) (d : ℤ) :
    laurentToRatFunc (C (c : ℂ) * T d) =
      (rationalEpsilonMonomial c d : RationalFunctions) := by
  rw [map_mul, laurentToRatFunc_C, laurentToRatFunc_T, coe_rationalEpsilonMonomial]
  rfl

/-- The retained clearing unit is the first monomial divided by the reflected
second monomial. -/
theorem clearedProductMultiplierUnit_rational (q c₁ : ℂˣ) (d₁ : ℤ)
    (c₂ : ℂˣ) (d₂ : ℤ) :
    laurentToRatFunc (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂) :
      LaurentPolynomial ℂ) =
      (rationalEpsilonMonomial c₁ d₁ : RationalFunctions) /
        RationalReflection.subst q⁻¹ (rationalEpsilonMonomial c₂ d₂) := by
  have hne : RationalReflection.subst q⁻¹
      (rationalEpsilonMonomial c₂ d₂ : RationalFunctions) ≠ 0 :=
    (map_ne_zero _).mpr (rationalEpsilonMonomial c₂ d₂).ne_zero
  apply (eq_div_iff hne).mpr
  rw [coe_clearedProductMultiplierUnit, clearedProductMultiplier_eq, map_mul,
    laurentToRatFunc_epsilon]
  have hi := congrArg laurentToRatFunc (inverseReflectedMonomial_mul q c₂ d₂)
  rw [map_mul, map_one, laurentToRatFunc_reflection,
    laurentToRatFunc_epsilon] at hi
  calc
    _ = (laurentToRatFunc (inverseReflectedMonomial q c₂ d₂) *
        RationalReflection.subst q⁻¹ (rationalEpsilonMonomial c₂ d₂)) *
          (rationalEpsilonMonomial c₁ d₁ : RationalFunctions) := by ring
    _ = _ := by rw [hi, one_mul]

/-- Separate the minus-one signs in the retained unit. -/
theorem clearedProductMultiplierUnit_sign (q ζ₁ c₁ : ℂˣ) (d₁ : ℤ)
    (ζ₂ c₂ : ℂˣ) (d₂ : ℤ) (e : ℕ) (hζ₂ : ζ₂ ^ 2 = 1) :
    laurentToRatFunc (↑(clearedProductMultiplierUnit q (ζ₁ ^ e * c₁) d₁
      (ζ₂ ^ e * c₂) d₂) : LaurentPolynomial ℂ) =
      RatFunc.C (((ζ₁ * ζ₂ : ℂˣ) : ℂ) ^ e) *
        ((rationalEpsilonMonomial c₁ d₁ : RationalFunctions) /
          RationalReflection.subst q⁻¹ (rationalEpsilonMonomial c₂ d₂)) := by
  have hz : (ζ₂ : ℂ)⁻¹ = (ζ₂ : ℂ) := by
    have hh : (ζ₂ : ℂ) * (ζ₂ : ℂ) = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_two, Units.val_mul] using
        congrArg (fun z : ℂˣ => (z : ℂ)) hζ₂
    exact inv_eq_of_mul_eq_one_right hh
  have hzC : (RatFunc.C (ζ₂ : ℂ))⁻¹ = RatFunc.C (ζ₂ : ℂ) := by
    rw [← map_inv₀, hz]
  have hC (c : ℂ) : RationalReflection.subst q⁻¹ (RatFunc.C c) = RatFunc.C c :=
    (RationalReflection.subst q⁻¹).commutes c
  rw [clearedProductMultiplierUnit_rational]
  simp only [coe_rationalEpsilonMonomial, Units.val_mul, Units.val_pow_eq_pow_val,
    map_mul, map_pow, RatFunc.algebraMap_eq_C, hC, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, hzC]
  ring

/-- Rational comparison after removing the complete polynomial factors. -/
theorem reflectedComparison_gammaProduct (q ζ₁ c₁ : ℂˣ) (d₁ : ℤ)
    (ζ₂ c₂ : ℂˣ) (d₂ : ℤ) (e : ℕ) (hζ₂ : ζ₂ ^ 2 = 1)
    {P₁ P₁D P₂ P₂D : Polynomial ℂ} (hP₁D : P₁D ≠ 0)
    (hP₂ : P₂ ≠ 0) (hP₂D : P₂D ≠ 0)
    {R RD G₂ : RationalFunctions}
    (hG₂ : G₂ * RationalReflection.subst q⁻¹
      (rationalGammaExpression q⁻¹ c₂ d₂ P₂D P₂) = 1)
    (hclear : RationalReflection.subst q⁻¹
        (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
      laurentToRatFunc (↑(clearedProductMultiplierUnit q (ζ₁ ^ e * c₁) d₁
        (ζ₂ ^ e * c₂) d₂) : LaurentPolynomial ℂ) *
          laurentToRatFunc (P₁ * P₂).toLaurent * R) :
    RationalReflection.subst q⁻¹ RD =
      RatFunc.C (((ζ₁ * ζ₂ : ℂˣ) : ℂ) ^ e) *
        ((rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D * G₂) * R) := by
  have hA : RationalReflection.subst q⁻¹
      (algebraMap (Polynomial ℂ) RationalFunctions P₁D) ≠ 0 :=
    (map_ne_zero _).mpr (RatFunc.algebraMap_ne_zero hP₁D)
  have hB : algebraMap (Polynomial ℂ) RationalFunctions P₂ ≠ 0 :=
    RatFunc.algebraMap_ne_zero hP₂
  have hBD : RationalReflection.subst q⁻¹
      (algebraMap (Polynomial ℂ) RationalFunctions P₂D) ≠ 0 :=
    (map_ne_zero _).mpr (RatFunc.algebraMap_ne_zero hP₂D)
  have hE : RationalReflection.subst q⁻¹
      (rationalEpsilonMonomial c₂ d₂ : RationalFunctions) ≠ 0 :=
    (map_ne_zero _).mpr (rationalEpsilonMonomial c₂ d₂).ne_zero
  rw [rationalGammaExpression, ← RationalReflection.subst_polynomial,
    map_div₀, map_mul, RationalReflection.subst_subst] at hG₂
  have hG₂eq : G₂ = algebraMap (Polynomial ℂ) RationalFunctions P₂ /
      (RationalReflection.subst q⁻¹ (rationalEpsilonMonomial c₂ d₂) *
        RationalReflection.subst q⁻¹
          (algebraMap (Polynomial ℂ) RationalFunctions P₂D)) := by
    apply (eq_div_iff (mul_ne_zero hE hBD)).mpr
    field_simp [hB] at hG₂
    simpa only [mul_assoc] using hG₂
  rw [clearedProductMultiplierUnit_sign q ζ₁ c₁ d₁ ζ₂ c₂ d₂ e hζ₂] at hclear
  simp only [laurentToRatFunc_toLaurent, map_mul] at hclear
  rw [hG₂eq, rationalGammaExpression, ← RationalReflection.subst_polynomial]
  apply (mul_left_cancel₀ (mul_ne_zero hA hBD))
  field_simp [hA, hBD, hE] at hclear ⊢
  linear_combination hclear

/-- The algebraic implication used with a retained integral comparison. -/
def ReflectedGammaProductLaw (q ζ₁ c₁ : ℂˣ) (d₁ : ℤ)
    (ζ₂ c₂ : ℂˣ) (d₂ : ℤ) (e : ℕ) : Prop :=
  ∀ (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    P₁D ≠ 0 → P₂ ≠ 0 → P₂D ≠ 0 →
    ∀ (R RD G₂ : RationalFunctions),
      G₂ * RationalReflection.subst q⁻¹
        (rationalGammaExpression q⁻¹ c₂ d₂ P₂D P₂) = 1 →
      RationalReflection.subst q⁻¹
          (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
        laurentToRatFunc (↑(clearedProductMultiplierUnit q (ζ₁ ^ e * c₁) d₁
          (ζ₂ ^ e * c₂) d₂) : LaurentPolynomial ℂ) *
            laurentToRatFunc (P₁ * P₂).toLaurent * R →
      RationalReflection.subst q⁻¹ RD =
        RatFunc.C (((ζ₁ * ζ₂ : ℂˣ) : ℂ) ^ e) *
          ((rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D * G₂) * R)

theorem reflectedGammaProductLaw (q ζ₁ c₁ : ℂˣ) (d₁ : ℤ)
    (ζ₂ c₂ : ℂˣ) (d₂ : ℤ) (e : ℕ) (hζ₂ : ζ₂ ^ 2 = 1) :
    ReflectedGammaProductLaw q ζ₁ c₁ d₁ ζ₂ c₂ d₂ e := by
  intro P₁ P₁D P₂ P₂D hP₁D hP₂ hP₂D R RD G₂ hG₂ hclear
  exact reflectedComparison_gammaProduct q ζ₁ c₁ d₁ ζ₂ c₂ d₂ e hζ₂
    hP₁D hP₂ hP₂D hG₂ hclear

end Langlands.RankinSelberg.DominantRankTransport
