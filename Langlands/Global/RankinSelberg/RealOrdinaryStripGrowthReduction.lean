import Langlands.Global.Factors.CuspidalPairPoleFromLocalTests
import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.RealWhittakerModelUniformityStatement

/-! # Real ordinary normalized strip growth from character-list growth -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal

namespace Langlands.LocalFactor.Archimedean

private theorem norm_Gamma_le_add_nat (s : ℂ) (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖s + (n : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (s + (n : ℂ))
      simp only [Complex.add_im, Complex.natCast_im, add_zero] at h
      exact hs.trans h
    have hnz : s + (n : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hn))
    apply ih.trans
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hnz, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hn

/-- The complex Gamma function is bounded on every vertical strip away from the real axis. -/
theorem stripGrowth_Gamma : HasStripExponentialGrowth Complex.Gamma := by
  intro a b
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < a + n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (-a)
    exact ⟨n, by linarith⟩
  obtain ⟨C, hC, hB⟩ := norm_Gamma_le_on_strip (a := a + n) (b := b + n) hn
  refine ⟨C, 0, 1, hC, le_rfl, fun s ha hb ht => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  refine (norm_Gamma_le_add_nat s ht n).trans (hB _ ?_ ?_)
  · simp only [Complex.add_re, Complex.natCast_re]
    linarith
  · simp only [Complex.add_re, Complex.natCast_re]
    linarith

private theorem stripGrowth_cpow_neg (p : ℝ) (hp : 1 ≤ p) :
    HasStripExponentialGrowth (fun s => (p : ℂ) ^ (-s)) := by
  intro a b
  refine ⟨p ^ (-a), 0, 0, by positivity, le_rfl, fun s ha _ _ => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hp), zero_mul, Real.exp_zero,
    mul_one, Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le hp (neg_le_neg ha)

/-- The real archimedean Gamma factor `π^(-s/2) Γ(s/2)` has exponential strip growth. -/
theorem stripGrowth_Gammaℝ : HasStripExponentialGrowth Complex.Gammaℝ := by
  have hΓ := stripGrowth_Gamma.div_add 0 (c := 2) (by norm_num)
  have hπ := (stripGrowth_cpow_neg Real.pi (by linarith [Real.one_le_pi_div_two])).div_add 0
    (c := 2) (by norm_num)
  have heq : Complex.Gammaℝ =
      (fun s : ℂ => (Real.pi : ℂ) ^ (-(s / 2))) * (fun s : ℂ => Complex.Gamma (s / 2)) := by
    funext s
    rw [Complex.Gammaℝ_def, Pi.mul_apply, neg_div]
  rw [heq]
  simpa only [add_zero, Complex.ofReal_ofNat] using hπ.mul hΓ

/-- The complex archimedean Gamma factor `2 (2π)^(-s) Γ(s)` has exponential strip growth. -/
theorem stripGrowth_Gammaℂ : HasStripExponentialGrowth Complex.Gammaℂ := by
  have hπ := stripGrowth_cpow_neg (2 * Real.pi) (by linarith [Real.one_le_pi_div_two])
  have heq : Complex.Gammaℂ = (fun _ : ℂ => (2 : ℂ)) *
      ((fun s : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-s)) * Complex.Gamma) := by
    funext s
    simp only [Complex.Gammaℂ_def, Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc]
  rw [heq]
  exact (HasStripExponentialGrowth.const 2).mul (hπ.mul stripGrowth_Gamma)

/-- The reciprocal of the denominator of a shifted Gamma block, that is the shifted Gamma
factor itself, has exponential strip growth. -/
theorem GammaBlock.stripGrowth_inv_denominator (b : GammaBlock) :
    HasStripExponentialGrowth (fun s => (b.factor.denominator s)⁻¹) := by
  cases b with
  | real d =>
    change HasStripExponentialGrowth (fun s => ((Complex.Gammaℝ (s + d))⁻¹)⁻¹)
    simp only [inv_inv]
    simpa only [Complex.ofReal_one, div_one] using stripGrowth_Gammaℝ.div_add d (c := 1) one_pos
  | complex d =>
    change HasStripExponentialGrowth (fun s => ((Complex.Gammaℂ (s + d))⁻¹)⁻¹)
    simp only [inv_inv]
    simpa only [Complex.ofReal_one, div_one] using stripGrowth_Gammaℂ.div_add d (c := 1) one_pos

/-- A finite product of Gamma factors has exponential strip growth. -/
theorem stripGrowth_gammaProduct_inv_denominator (bs : List GammaBlock) :
    HasStripExponentialGrowth (fun s => ((gammaProduct bs).denominator s)⁻¹) := by
  induction bs with
  | nil =>
    change HasStripExponentialGrowth (fun _ => (1 : ℂ)⁻¹)
    exact HasStripExponentialGrowth.const _
  | cons b bs ih =>
    have heq : (fun s => ((gammaProduct (b :: bs)).denominator s)⁻¹) =
        (fun s => (b.factor.denominator s)⁻¹) * (fun s => ((gammaProduct bs).denominator s)⁻¹) := by
      funext s
      change (b.factor.denominator s * (gammaProduct bs).denominator s)⁻¹ = _
      rw [Pi.mul_apply, mul_inv]
    rw [heq]
    exact b.stripGrowth_inv_denominator.mul ih

/-- The real pair `L`-factor, the reciprocal of its entire denominator, has exponential strip
growth. -/
theorem stripGrowth_realPairLFactor_inv_denominator (xs ys : List RealBlock) :
    HasStripExponentialGrowth (fun s => ((realPairLFactor xs ys).denominator s)⁻¹) := by
  rw [realPairLFactor, realLFactor_eq_gammaProduct]
  exact stripGrowth_gammaProduct_inv_denominator _

end Langlands.LocalFactor.Archimedean

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealPrincipalSeries

/-- A real normalized pair gives the primal integral a meromorphic continuation of exponential
strip growth: the entire normalization divided by the pair `L`-denominator. -/
theorem RealJacquet.HasRealPairNormalizedGrowth.exists_meromorphic_stripGrowth
    {ds es dds ees : List RealBlock} {b : ℝˣ} {c : ℝ≥0} {hc : 0 < c} {sign : ℂ}
    {I Id : ℂ → ℂ} (h : RealJacquet.HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id) :
    ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ HasStripExponentialGrowth M ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I s = M s := by
  obtain ⟨N, _, hN, _, hNg, _, ⟨σ, hR⟩, _⟩ := h
  obtain ⟨τ, hτ⟩ :=
    FunctionalEquationComparison.CompletedEquationAdapter.realPairLFactor_denominator_ne_zero ds es
  refine ⟨fun s => N s * ((realPairLFactor ds es).denominator s)⁻¹, ?_, ?_, max σ τ,
    fun s hs => ?_⟩
  · intro s _
    exact (hN.analyticAt s).meromorphicAt.mul
      ((realPairLFactor ds es).entire.analyticAt s).meromorphicAt.inv
  · exact hNg.mul (stripGrowth_realPairLFactor_inv_denominator ds es)
  · have h₁ := (hR s ((le_max_left _ _).trans_lt hs)).1
    have h₂ := hτ s ((le_max_right _ _).trans_lt hs)
    show I s = N s * ((realPairLFactor ds es).denominator s)⁻¹
    rw [h₁, mul_comm ((realPairLFactor ds es).denominator s) (I s), mul_assoc,
      mul_inv_cancel₀ h₂, mul_one]

/-- Ordinary unequal-rank real tests: every entire normalization has exponential strip growth,
given model uniformity, the uniform principal-series inclusion and unequal character growth at
the two ranks. -/
theorem realOrdinaryUnequalTest_stripGrowth
    (hU : RealWhittakerModelUniformityStatement)
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    {r t : ℕ} (h : t < r) (hG : RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h)
    (d e : List RealBlock) (hd : realRank d = r + 1) (he : realRank e = t + 1) (a : ℝˣ)
    (D : RealQuotientMeasureData t) :
    HasOrdinaryNormalizationStripGrowth (realOrdinaryUnequalTest h d e a D)
      (realPairLFactor d e) := by
  refine hasOrdinaryNormalizationStripGrowth_real_of_raw _ d e fun i => ?_
  have hW := hI r d hd a (hU r d hd a i.1.2)
  have hW' := hI t e he (-a) (hU t e he (-a) i.2.2)
  exact (hG (expand d) (expand e) (RealJacquet.isRealCharacterList_expand d)
    (RealJacquet.isRealCharacterList_expand e) (by rw [realRank_expand]; exact hd)
    (by rw [realRank_expand]; exact he) a D i.1 i.2 hW hW').exists_meromorphic_stripGrowth

/-- Ordinary equal-rank real tests: every entire normalization has exponential strip growth,
given model uniformity, the uniform principal-series inclusion and equal character growth at
the rank. -/
theorem realOrdinaryEqualTest_stripGrowth
    (hU : RealWhittakerModelUniformityStatement)
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    {r : ℕ} (hG : RealJacquet.RealLocalEqualCharacterGrowthAtRank r)
    (d e : List RealBlock) (hd : realRank d = r + 1) (he : realRank e = r + 1) (a : ℝˣ)
    (D : RealQuotientMeasureData r) :
    HasOrdinaryNormalizationStripGrowth (realOrdinaryEqualTest r d e a D)
      (realPairLFactor d e) := by
  refine hasOrdinaryNormalizationStripGrowth_real_of_raw _ d e fun i => ?_
  have hW := hI r d hd a (hU r d hd a i.1.2)
  have hW' := hI r e he (-a) (hU r e he (-a) i.2.1.2)
  exact (hG (expand d) (expand e) (RealJacquet.isRealCharacterList_expand d)
    (RealJacquet.isRealCharacterList_expand e) (by rw [realRank_expand]; exact hd)
    (by rw [realRank_expand]; exact he) a D i.1 i.2.1 i.2.2 hW hW').exists_meromorphic_stripGrowth

/-- Real ordinary normalized strip growth from model uniformity, the uniform principal-series
inclusion, unequal character-list growth at all pairs of ranks and equal character-list growth
at all positive ranks. -/
def RealOrdinaryStripGrowthCharacterReductionStatement : Prop :=
  RealWhittakerModelUniformityStatement → RealUniformPrincipalSeriesInclusionStatement →
    (∀ (r t : ℕ) (h : t < r), RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h) →
    (∀ r : ℕ, 0 < r → RealJacquet.RealLocalEqualCharacterGrowthAtRank r) →
    CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement

theorem realOrdinaryStripGrowthCharacterReduction :
    RealOrdinaryStripGrowthCharacterReductionStatement := by
  intro hU hI hUnequal hEqual
  have hEqual' (r : ℕ) : RealJacquet.RealLocalEqualCharacterGrowthAtRank r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact RealJacquet.realLocalEqualCharacterGrowthAtRank_zero
    · exact hEqual r hr
  exact ⟨fun r t h d e hd he a =>
      realOrdinaryUnequalTest_stripGrowth hU hI h (hUnequal r t h) d e hd he a _,
    fun r d e hd he a => realOrdinaryEqualTest_stripGrowth hU hI (hEqual' r) d e hd he a _⟩

/-- Real ordinary normalized strip growth from model uniformity, the uniform principal-series
inclusion, the three premises of the real equal-rank successor step and unequal
character-list growth at all pairs of ranks. -/
def RealOrdinaryStripGrowthPremisesStatement : Prop :=
  RealWhittakerModelUniformityStatement → RealUniformPrincipalSeriesInclusionStatement →
    RealGodement.RealUniformCanonicalRangePremise →
    RealGodement.RealCanonicalStandardEvaluationPremise →
    (∀ t : ℕ, RealGodement.RealMatrixCoefficientGrowthPremise t) →
    (∀ (r t : ℕ) (h : t < r), RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h) →
    CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement

theorem realOrdinaryStripGrowthPremises : RealOrdinaryStripGrowthPremisesStatement := by
  intro hU hI hRange hEval hMat hUnequal
  refine realOrdinaryStripGrowthCharacterReduction hU hI hUnequal fun r hr => ?_
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  exact RealGodement.realLocalEqualGrowthStep t hRange hEval (hMat t)
    (hUnequal (t + 1) t (Nat.lt_succ_self t))

end Langlands.Global.RankinSelbergGlobal
