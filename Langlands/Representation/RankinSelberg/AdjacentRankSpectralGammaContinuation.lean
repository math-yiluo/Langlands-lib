import Langlands.Representation.RankinSelberg.AdjacentRankGammaEntireContinuation

/-! Explicit finite kernels for a product with one spectrally shifted gamma factor. -/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentGammaContinuation

open HarmonicAnalysis HarmonicAnalysis.BilateralLaurentSeries
open ParameterSpecialization LocalFactor Polynomial

/-- The fixed first factor times the actual spectral shift of the second. -/
def spectralGammaProduct (q : ℕ) (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) : RationalFunctions :=
  G₀ * rationalRescale (spectralShiftUnit q hq u) G₁

@[simp] theorem spectralGammaProduct_zero {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) :
    spectralGammaProduct q hq G₀ G₁ 0 = G₀ * G₁ := by
  have hunit : spectralShiftUnit q hq 0 = 1 := by
    apply Units.ext
    simp [spectralPoint]
  have hrescale : rationalRescale (1 : ℂˣ) G₁ = G₁ := by
    rw [rationalRescale_num_div_denom]
    simp [RatFunc.num_div_denom]
  simp only [spectralGammaProduct, hunit, hrescale]

/-- The product of the rescaled numerator polynomials presents the gamma
product over the corresponding product of denominator polynomials. -/
theorem spectralGammaProduct_presentation {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) :
    laurentToRatFunc (spectralClearingKernel q G₀.num G₁.num u) =
      laurentToRatFunc (spectralClearingKernel q G₀.denom G₁.denom u) *
        spectralGammaProduct q hq G₀ G₁ u := by
  have hnum (G : RationalFunctions) :
      algebraMap ℂ[X] RationalFunctions G.num =
        algebraMap ℂ[X] RationalFunctions G.denom * G :=
    ((div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero G))).mp
      (RatFunc.num_div_denom G)).trans (mul_comm _ _)
  have hshift := congrArg (rationalRescale (spectralShiftUnit q hq u)) (hnum G₁)
  simp only [map_mul, rationalRescale_algebraMap, coe_spectralShiftUnit] at hshift
  simp only [spectralClearingKernel, laurentToRatFunc_toLaurent, map_mul,
    spectralGammaProduct]
  rw [hnum G₀, hshift]
  ring

/-- The displayed spectral gamma denominator is nonzero at every parameter. -/
theorem spectralGammaProduct_denominator_ne_zero {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) :
    spectralClearingKernel q G₀.denom G₁.denom u ≠ 0 := by
  apply Polynomial.toLaurent_ne_zero.mpr
  apply mul_ne_zero (RatFunc.denom_ne_zero G₀)
  change polynomialRescale (spectralShiftUnit q hq u) G₁.denom ≠ 0
  simpa only [map_zero] using
    (polynomialRescale (spectralShiftUnit q hq u)).injective.ne
      (RatFunc.denom_ne_zero G₁)

/-- Continue the actual one-factor spectral gamma product to zero. All finite
gamma presentation kernels, their entireness, support bounds and nonvanishing
are supplied by the fixed rational factors. -/
theorem gammaFE_spectralProduct_at_zero
    {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    (G₀ G₁ : RationalFunctions) (P₀ P₁ : ℂ[X]) (hP : P₀ * P₁ ≠ 0)
    {a ad : ℂ → BilateralLaurentSeries}
    (hae : EntireCoefficientFamily a) (hade : EntireCoefficientFamily ad)
    {R Rd : ℂ → RationalFunctions} {I Id : ℂ → ℂ → ℂ}
    (hR : ∀ u, HasRationalContinuation q (I u) (R u))
    (hRd : ∀ u, HasRationalContinuation q (Id u) (Rd u))
    (ha : ∀ u, HasAbsoluteBilateralSpectralExpansion q (a u) (I u))
    (had : ∀ u, HasAbsoluteBilateralSpectralExpansion q (ad u) (Id u))
    (C : ℝ)
    (hclear : ∀ u : ℝ, C < u → ∃ L : LaurentPolynomial ℂ,
      spectralClearingKernel q P₀ P₁ (u : ℂ) • a (u : ℂ) =
        ofLaurentPolynomial L)
    (hFE : ∀ u : ℝ, C < u →
      GammaFunctionalEquation q ζ e (spectralGammaProduct q hq G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ))) :
    GammaFunctionalEquation q ζ e (G₀ * G₁) (R 0) (Rd 0) := by
  have hKzero : spectralClearingKernel q P₀ P₁ 0 ≠ 0 := by
    rw [spectralClearingKernel_zero]
    exact Polynomial.toLaurent_ne_zero.mpr hP
  simpa only [spectralGammaProduct_zero] using
    gammaFE_of_entire_real_ray hq
      (spectralClearingKernel_entire_uniform hq G₀.num G₁.num)
      (spectralClearingKernel_entire_uniform hq G₀.denom G₁.denom)
      (spectralClearingKernel_entire_uniform hq P₀ P₁) hae hade
      (spectralGammaProduct_presentation hq G₀ G₁) hR hRd ha had C hclear hFE 0
      (spectralGammaProduct_denominator_ne_zero hq G₀ G₁ 0) hKzero

end Langlands.RankinSelberg.AdjacentGammaContinuation
