import Langlands.Representation.RankinSelberg.AdjacentRankGammaLaurentBridge
import Langlands.Representation.RankinSelberg.AdjacentRankClearingKernel

/-! Coefficientwise entire continuation of gamma equations with retained kernels. -/

noncomputable section

namespace Langlands.RankinSelberg.ParameterSpecialization

open HarmonicAnalysis

/-- An entire finite Laurent kernel acts on entire coefficient families. -/
theorem EntireUniformLaurentKernel.smul
    {P : ℂ → LaurentPolynomial ℂ} (hP : EntireUniformLaurentKernel P)
    {a : ℂ → BilateralLaurentSeries} (ha : EntireCoefficientFamily a) :
    EntireCoefficientFamily (fun u => P u • a u) := by
  obtain ⟨S, hS, hcoeff⟩ := hP
  exact laurent_smul_entire S P a hS (fun j _ => hcoeff j) ha

end Langlands.RankinSelberg.ParameterSpecialization

namespace Langlands.RankinSelberg.AdjacentGammaContinuation

open HarmonicAnalysis HarmonicAnalysis.BilateralLaurentSeries
open TwoBlockFirstBlockLaurent LocalFactor ParameterSpecialization

/-- The gamma coefficient identity retains both finite denominator kernels. -/
def ClearedGammaCoefficientIdentity (q : ℕ) (ζ : ℂˣ) (e : ℕ)
    (A B K : LaurentPolynomial ℂ) (a ad : BilateralLaurentSeries) : Prop :=
  (B * K) • reflectSeries q ad =
    (LaurentPolynomial.C ((ζ : ℂ) ^ e) * A * K) • a

/-- Reflection preserves entire dependence of every coefficient. -/
theorem reflectSeries_entire {q : ℕ} {a : ℂ → BilateralLaurentSeries}
    (ha : EntireCoefficientFamily a) :
    EntireCoefficientFamily (fun u => reflectSeries q (a u)) := by
  intro m u
  exact analyticAt_const.mul (ha (-m) u)

/-- A cleared gamma identity on a real ray extends coefficientwise to every
complex parameter. The three finite kernel actions are applied sequentially. -/
theorem cleared_gamma_identity_of_entire_real_ray
    {q : ℕ} {ζ : ℂˣ} {e : ℕ}
    {A B K : ℂ → LaurentPolynomial ℂ}
    (hA : EntireUniformLaurentKernel A) (hB : EntireUniformLaurentKernel B)
    (hK : EntireUniformLaurentKernel K)
    {a ad : ℂ → BilateralLaurentSeries}
    (ha : EntireCoefficientFamily a) (had : EntireCoefficientFamily ad)
    (C : ℝ)
    (hreal : ∀ u : ℝ, C < u →
      ClearedGammaCoefficientIdentity q ζ e (A (u : ℂ)) (B (u : ℂ))
        (K (u : ℂ)) (a (u : ℂ)) (ad (u : ℂ)))
    (z : ℂ) :
    ClearedGammaCoefficientIdentity q ζ e (A z) (B z) (K z) (a z) (ad z) := by
  have hleft := hB.smul (hK.smul (reflectSeries_entire (q := q) had))
  have hAK := hA.smul (hK.smul ha)
  have hright : EntireCoefficientFamily (fun u =>
      LaurentPolynomial.C ((ζ : ℂ) ^ e) • (A u • (K u • a u))) := by
    intro m u
    simp only [C_smul, smul_apply]
    exact analyticAt_const.mul (hAK m u)
  have hall := coefficientFamily_eq_of_real_gt hleft hright C (by
    intro u hu m
    have he := congrArg (fun c : BilateralLaurentSeries => c m) (hreal u hu)
    simpa only [mul_smul] using he)
  simpa only [ClearedGammaCoefficientIdentity, mul_smul] using congrFun hall z

/-- Actual gamma equations on a real parameter ray continue to every parameter
where the retained denominator kernels are nonzero. Original and dual spectral
expansions may converge on different half-planes. -/
theorem gammaFE_of_entire_real_ray
    {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {A B K : ℂ → LaurentPolynomial ℂ}
    (hA : EntireUniformLaurentKernel A) (hB : EntireUniformLaurentKernel B)
    (hK : EntireUniformLaurentKernel K)
    {a ad : ℂ → BilateralLaurentSeries}
    (hae : EntireCoefficientFamily a) (hade : EntireCoefficientFamily ad)
    {G R Rd : ℂ → RationalFunctions} {I Id : ℂ → ℂ → ℂ}
    (hG : ∀ u, laurentToRatFunc (A u) = laurentToRatFunc (B u) * G u)
    (hR : ∀ u, HasRationalContinuation q (I u) (R u))
    (hRd : ∀ u, HasRationalContinuation q (Id u) (Rd u))
    (ha : ∀ u, HasAbsoluteBilateralSpectralExpansion q (a u) (I u))
    (had : ∀ u, HasAbsoluteBilateralSpectralExpansion q (ad u) (Id u))
    (C : ℝ)
    (hclear : ∀ u : ℝ, C < u → ∃ L : LaurentPolynomial ℂ,
      K (u : ℂ) • a (u : ℂ) = ofLaurentPolynomial L)
    (hFE : ∀ u : ℝ, C < u →
      GammaFunctionalEquation q ζ e (G (u : ℂ)) (R (u : ℂ)) (Rd (u : ℂ)))
    (z : ℂ) (hBz : B z ≠ 0) (hKz : K z ≠ 0) :
    GammaFunctionalEquation q ζ e (G z) (R z) (Rd z) := by
  obtain ⟨S, hS, hcoeff⟩ := hK
  obtain ⟨L, hL, -, -⟩ := laurent_clearing_of_real_gt S K a hS
    (fun j _ => hcoeff j) hae C (by
      intro u hu
      obtain ⟨L, hL⟩ := hclear u hu
      exact ⟨L, hL.symm⟩)
  have hidentity := cleared_gamma_identity_of_entire_real_ray hA hB
    ⟨S, hS, hcoeff⟩ hae hade C (by
      intro u hu
      exact gammaFE_cleared_coefficient_identity hq (hG (u : ℂ))
        (hR (u : ℂ)) (hRd (u : ℂ)) (ha (u : ℂ)) (had (u : ℂ))
        (hL (u : ℂ)).symm (hFE u hu)) z
  exact gammaFE_of_cleared_coefficient_identity hq hBz hKz (hG z)
    (hR z) (hRd z) (ha z).to_spectral (had z).to_spectral (hL z).symm hidentity

end Langlands.RankinSelberg.AdjacentGammaContinuation
