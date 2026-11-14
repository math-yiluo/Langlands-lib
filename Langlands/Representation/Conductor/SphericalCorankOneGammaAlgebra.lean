import Langlands.Representation.RankinSelberg.RationalGammaExpressionProduct
import Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra
import Langlands.Representation.RankinSelberg.SpectralRescaling

/-!
# Rational-function algebra for the spherical corank-one functional equation

Three identities of rational functions used to assemble JPSS 1981, (4.2), display (3):
rescaling the explicit gamma expression `c X^m P(X) / P̃(δ/X)` by `X ↦ zX`, the
product of the rescaled expressions over a tuple `x`, and the passage from a gamma
functional equation with this explicit gamma factor to the normalized functional
equation with the two products of rescaled polynomials.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open Langlands.RankinSelberg Langlands.LocalFactor Polynomial

/-- Rescaling `X ↦ zX` turns `c X^m P(X) / P̃(δ/X)` into
`(c z^m) X^m P(zX) / P̃(z⁻¹ δ/X)`. -/
theorem rationalRescale_rationalGammaExpression (δ c z : ℂˣ) (m : ℤ) (P Pdual : ℂ[X]) :
    rationalRescale z (rationalGammaExpression δ c m P Pdual) =
      rationalGammaExpression δ (c * z ^ m) m (P.comp (C (z : ℂ) * X))
        (Pdual.comp (C ((z⁻¹ : ℂˣ) : ℂ) * X)) := by
  unfold rationalGammaExpression
  rw [map_div₀, map_mul, rationalRescale_algebraMap, ← aeval_algHom_apply, aeval_comp]
  have hX : (RatFunc.X : RationalFunctions) ≠ 0 := RatFunc.X_ne_zero
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hzC : (RatFunc.C (z : ℂ) : RationalFunctions) ≠ 0 := by
    simp [hz]
  congr 2
  · simp only [coe_rationalEpsilonMonomial, map_mul, map_zpow₀, Units.val_mul,
      Units.val_zpow_eq_zpow_val, RatFunc.algebraMap_eq_C, rationalRescale_C,
      rationalRescale_X, mul_zpow, map_zpow₀]
    ring
  · congr 1
    simp only [RationalReflection.reflectedVariable, map_div₀, rationalRescale_C,
      rationalRescale_X, aeval_mul, aeval_C, aeval_X, Units.val_inv_eq_inv_val,
      RatFunc.algebraMap_eq_C, map_inv₀]
    field_simp

/-- The product over a tuple `x` of the rescaled gamma expressions is the gamma
expression with constant `c^(n+1) (∏ x_i)^m`, exponent `(n+1) m` and the two products
of rescaled polynomials. -/
theorem prod_rationalRescale_rationalGammaExpression {n : ℕ} (δ c : ℂˣ) (m : ℤ)
    (P Pdual : ℂ[X]) (x : Fin (n + 1) → ℂˣ) :
    ∏ i, rationalRescale (x i) (rationalGammaExpression δ c m P Pdual) =
      rationalGammaExpression δ (c ^ (n + 1) * (∏ i, x i) ^ m) (((n + 1 : ℕ) : ℤ) * m)
        (∏ i, P.comp (C (x i : ℂ) * X)) (∏ i, Pdual.comp (C ((x⁻¹ i : ℂˣ) : ℂ) * X)) := by
  simp only [rationalRescale_rationalGammaExpression]
  rw [← TemperedLFactorGamma.rationalGammaExpression_prod]
  congr 1
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_zpow]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open GammaNormalization in
/-- A gamma functional equation whose gamma factor is the explicit expression
`c X^m P(X) / P̃(δ/X)`, `δ = q⁻¹`, and whose sign is one, is the normalized functional
equation with polynomials `P`, `P̃`, sign `1` with exponent `0`, and monomial `c X^m`. -/
theorem normalizedFunctionalEquation_of_gammaFunctionalEquation {q : ℕ} (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {ζ : ℂˣ} {e : ℕ} (hζ : (ζ : ℂ) ^ e = 1)
    {c : ℂˣ} {m : ℤ} {P Pdual : ℂ[X]} (hPd : Pdual ≠ 0) {R Rdual : RationalFunctions}
    (h : GammaFunctionalEquation q ζ e (rationalGammaExpression δ c m P Pdual) R Rdual) :
    NormalizedFunctionalEquation q P Pdual 1 c 0 m R Rdual := by
  intro s hR hRd
  have hid := rational_identity_of_gammaFunctionalEquation hq hδ h
  rw [hζ, map_one, one_mul] at hid
  have hPd0 : RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions Pdual) =
      aeval (RationalReflection.reflectedVariable δ) Pdual :=
    RationalReflection.subst_polynomial δ Pdual
  have hprod : RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions Pdual * Rdual) =
      RatFunc.C (c : ℂ) * RatFunc.X ^ m * (algebraMap ℂ[X] RationalFunctions P * R) := by
    rw [map_mul (RationalReflection.subst δ), hid, hPd0]
    have hA : (aeval (RationalReflection.reflectedVariable δ) Pdual : RationalFunctions) ≠ 0 := by
      intro h0
      apply hPd
      apply (transcendental_iff_injective.mp (RationalReflection.variable_transcendental δ))
      rw [h0, map_zero]
    unfold rationalGammaExpression
    rw [coe_rationalEpsilonMonomial, RatFunc.algebraMap_eq_C]
    field_simp
  -- Evaluate the rational identity at the spectral point.
  have hz := spectralPoint_ne_zero hq s
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [hδ, spectralPoint_one_sub hq]
  have hRd' : RationalEvaluation.RegularAt Rdual ((δ : ℂ) / spectralPoint q s) := by
    rw [href]; exact hRd
  have hPdreg : RationalEvaluation.RegularAt (algebraMap ℂ[X] RationalFunctions Pdual)
      ((δ : ℂ) / spectralPoint q s) :=
    RationalEvaluation.RegularAt.polynomial Pdual
  have hPreg : RationalEvaluation.RegularAt (algebraMap ℂ[X] RationalFunctions P)
      (spectralPoint q s) :=
    RationalEvaluation.RegularAt.polynomial P
  have hCreg : RationalEvaluation.RegularAt (RatFunc.C (c : ℂ)) (spectralPoint q s) := by
    simpa using (RationalEvaluation.RegularAt.polynomial (z := spectralPoint q s) (C (c : ℂ)))
  have hXev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) RatFunc.X ≠ 0 := by
    rw [RatFunc.eval_X]; exact hz
  have hXreg : RationalEvaluation.RegularAt (RatFunc.X ^ m : RationalFunctions)
      (spectralPoint q s) :=
    RationalEvaluation.RegularAt.zpow hXev m
  have hev := congrArg (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)) hprod
  rw [RationalEvaluation.eval_subst δ hz (hPdreg.mul hRd'),
    RationalEvaluation.eval_mul hPdreg hRd',
    RationalEvaluation.eval_mul (hCreg.mul hXreg) (hPreg.mul hR),
    RationalEvaluation.eval_mul hCreg hXreg, RationalEvaluation.eval_mul hPreg hR,
    RationalEvaluation.eval_zpow hXev, RatFunc.eval_C, RatFunc.eval_X,
    eval_algebraMap_polynomial, eval_algebraMap_polynomial, RingHom.id_apply, href] at hev
  rw [hev, epsilonMonomial]
  simp

end Langlands.Conductor.SphericalCorankOne
