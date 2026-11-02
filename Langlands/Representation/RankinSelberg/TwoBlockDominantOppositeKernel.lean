import Langlands.Representation.RankinSelberg.AdjacentRankGammaEntireContinuation

noncomputable section

namespace Langlands.RankinSelberg.ParameterSpecialization

open HarmonicAnalysis Polynomial

/-- Both block denominators are rescaled, with the opposite parameters. -/
def oppositeSpectralClearingKernel (q : ℕ) (P₀ P₁ : Polynomial ℂ) (u : ℂ) :
    LaurentPolynomial ℂ :=
  (P₀.comp (C (spectralPoint q (-u)) * X) *
    P₁.comp (C (spectralPoint q u) * X)).toLaurent

@[simp]
theorem oppositeSpectralClearingKernel_zero (q : ℕ) (P₀ P₁ : Polynomial ℂ) :
    oppositeSpectralClearingKernel q P₀ P₁ 0 = (P₀ * P₁).toLaurent := by
  simp [oppositeSpectralClearingKernel, spectralPoint]

private theorem toLaurent_coeff_nat (P : Polynomial ℂ) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

private theorem toLaurent_coeff_negSucc (P : Polynomial ℂ) (n : ℕ) :
    P.toLaurent.coeff (Int.negSucc n) = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  change (k : ℤ) = Int.negSucc n at hk
  omega

/-- The actual opposite-twist product has entire coefficients and a fixed
finite exponent set. -/
theorem oppositeSpectralClearingKernel_entire_uniform
    {q : ℕ} (hq : 1 < q) (P₀ P₁ : Polynomial ℂ) :
    EntireUniformLaurentKernel (oppositeSpectralClearingKernel q P₀ P₁) := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hpoint : Differentiable ℂ (spectralPoint q) :=
    (TwoBlockDeformation.differentiable_ofReal_cpow hqpos).comp differentiable_id.neg
  have hrescale (P : Polynomial ℂ) (n : ℕ) :
      Differentiable ℂ (fun u => (P.comp (C (spectralPoint q u) * X)).coeff n) := by
    simp only [Polynomial.comp_C_mul_X_coeff]
    exact (hpoint.pow n).const_mul (P.coeff n)
  have hproduct : ∀ n : ℕ, Differentiable ℂ (fun u =>
      (P₀.comp (C (spectralPoint q (-u)) * X) *
        P₁.comp (C (spectralPoint q u) * X)).coeff n) := by
    intro n
    simp only [Polynomial.coeff_mul]
    exact Differentiable.fun_sum fun j _ =>
      ((hrescale P₀ j.1).comp differentiable_id.neg).mul (hrescale P₁ j.2)
  have hdegree (P : Polynomial ℂ) (u : ℂ) :
      (P.comp (C (spectralPoint q u) * X)).natDegree ≤ P.natDegree := by
    have hsmall : (C (spectralPoint q u) * X : Polynomial ℂ).natDegree ≤ 1 := by
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] using
        (Polynomial.natDegree_mul_le (p := C (spectralPoint q u)) (q := X))
    calc
      _ ≤ P.natDegree * (C (spectralPoint q u) * X : Polynomial ℂ).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hsmall
      _ = P.natDegree := mul_one _
  refine ⟨(Finset.range (P₀.natDegree + P₁.natDegree + 1)).map Nat.castEmbedding, ?_, ?_⟩
  · intro u m hm
    rw [oppositeSpectralClearingKernel, LaurentPolynomial.support_coeff_toLaurent] at hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hm
    refine Finset.mem_map.mpr ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hnle := Polynomial.le_natDegree_of_mem_supp _ hn
    have hprod := Polynomial.natDegree_mul_le
      (p := P₀.comp (C (spectralPoint q (-u)) * X))
      (q := P₁.comp (C (spectralPoint q u) * X))
    have h0 := hdegree P₀ (-u)
    have h1 := hdegree P₁ u
    omega
  · intro j u
    cases j with
    | ofNat n =>
      change AnalyticAt ℂ (fun z =>
        (oppositeSpectralClearingKernel q P₀ P₁ z).coeff (n : ℤ)) u
      simpa only [oppositeSpectralClearingKernel, toLaurent_coeff_nat] using
        (hproduct n).analyticAt u
    | negSucc n =>
      simp only [oppositeSpectralClearingKernel, toLaurent_coeff_negSucc]
      exact analyticAt_const

/-- Real-ray clearing by the actual opposite kernel specializes to the
original block product at zero. -/
theorem oppositeSpectralKernel_laurent_clearing_at_zero
    {q : ℕ} (hq : 1 < q) (P₀ P₁ : Polynomial ℂ)
    (c : ℂ → BilateralLaurentSeries) (hc : EntireCoefficientFamily c) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        oppositeSpectralClearingKernel q P₀ P₁ (u : ℂ) • c (u : ℂ)) :
    ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = (P₀ * P₁).toLaurent • c 0 := by
  obtain ⟨S, hS, hA⟩ := oppositeSpectralClearingKernel_entire_uniform hq P₀ P₁
  obtain ⟨Q, hQ, -, -⟩ := laurent_clearing_of_real_gt S
    (oppositeSpectralClearingKernel q P₀ P₁) c hS (fun j _ => hA j) hc C hreal
  exact ⟨Q 0, by simpa only [oppositeSpectralClearingKernel_zero] using hQ 0⟩

end Langlands.RankinSelberg.ParameterSpecialization

namespace Langlands.RankinSelberg.AdjacentGammaContinuation

open HarmonicAnalysis HarmonicAnalysis.BilateralLaurentSeries
open ParameterSpecialization LocalFactor Polynomial

/-- The product of the two actual opposite spectral shifts. -/
def oppositeSpectralGammaProduct (q : ℕ) (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) : RationalFunctions :=
  rationalRescale (spectralShiftUnit q hq (-u)) G₀ *
    rationalRescale (spectralShiftUnit q hq u) G₁

@[simp]
theorem oppositeSpectralGammaProduct_zero {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) :
    oppositeSpectralGammaProduct q hq G₀ G₁ 0 = G₀ * G₁ := by
  have hunit : spectralShiftUnit q hq 0 = 1 := by
    apply Units.ext
    simp [spectralPoint]
  have hrescale (G : RationalFunctions) : rationalRescale (1 : ℂˣ) G = G := by
    rw [rationalRescale_num_div_denom]
    simp [RatFunc.num_div_denom]
  simp only [oppositeSpectralGammaProduct, neg_zero, hunit, hrescale]

/-- The rescaled numerator and denominator products present the exact gamma
product without any denominator cancellation. -/
theorem oppositeSpectralGammaProduct_presentation {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) :
    laurentToRatFunc (oppositeSpectralClearingKernel q G₀.num G₁.num u) =
      laurentToRatFunc (oppositeSpectralClearingKernel q G₀.denom G₁.denom u) *
        oppositeSpectralGammaProduct q hq G₀ G₁ u := by
  have hnum (G : RationalFunctions) :
      algebraMap ℂ[X] RationalFunctions G.num =
        algebraMap ℂ[X] RationalFunctions G.denom * G :=
    ((div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero G))).mp
      (RatFunc.num_div_denom G)).trans (mul_comm _ _)
  have hshift0 := congrArg (rationalRescale (spectralShiftUnit q hq (-u))) (hnum G₀)
  have hshift1 := congrArg (rationalRescale (spectralShiftUnit q hq u)) (hnum G₁)
  simp only [map_mul, rationalRescale_algebraMap, coe_spectralShiftUnit] at hshift0 hshift1
  simp only [oppositeSpectralClearingKernel, laurentToRatFunc_toLaurent, map_mul,
    oppositeSpectralGammaProduct]
  rw [hshift0, hshift1]
  ring

theorem oppositeSpectralGammaProduct_denominator_ne_zero {q : ℕ} (hq : 1 < q)
    (G₀ G₁ : RationalFunctions) (u : ℂ) :
    oppositeSpectralClearingKernel q G₀.denom G₁.denom u ≠ 0 := by
  apply Polynomial.toLaurent_ne_zero.mpr
  apply mul_ne_zero
  · change polynomialRescale (spectralShiftUnit q hq (-u)) G₀.denom ≠ 0
    simpa only [map_zero] using
      (polynomialRescale (spectralShiftUnit q hq (-u))).injective.ne
        (RatFunc.denom_ne_zero G₀)
  · change polynomialRescale (spectralShiftUnit q hq u) G₁.denom ≠ 0
    simpa only [map_zero] using
      (polynomialRescale (spectralShiftUnit q hq u)).injective.ne
        (RatFunc.denom_ne_zero G₁)

/-- The entire coefficient continuation theorem applies to the opposite
product, with every finite presentation kernel supplied explicitly. -/
theorem gammaFE_oppositeSpectralProduct_at_zero
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
      oppositeSpectralClearingKernel q P₀ P₁ (u : ℂ) • a (u : ℂ) =
        ofLaurentPolynomial L)
    (hFE : ∀ u : ℝ, C < u →
      GammaFunctionalEquation q ζ e (oppositeSpectralGammaProduct q hq G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ))) :
    GammaFunctionalEquation q ζ e (G₀ * G₁) (R 0) (Rd 0) := by
  have hKzero : oppositeSpectralClearingKernel q P₀ P₁ 0 ≠ 0 := by
    rw [oppositeSpectralClearingKernel_zero]
    exact Polynomial.toLaurent_ne_zero.mpr hP
  simpa only [oppositeSpectralGammaProduct_zero] using
    gammaFE_of_entire_real_ray hq
      (oppositeSpectralClearingKernel_entire_uniform hq G₀.num G₁.num)
      (oppositeSpectralClearingKernel_entire_uniform hq G₀.denom G₁.denom)
      (oppositeSpectralClearingKernel_entire_uniform hq P₀ P₁) hae hade
      (oppositeSpectralGammaProduct_presentation hq G₀ G₁) hR hRd ha had C hclear hFE 0
      (oppositeSpectralGammaProduct_denominator_ne_zero hq G₀ G₁ 0) hKzero

end Langlands.RankinSelberg.AdjacentGammaContinuation
