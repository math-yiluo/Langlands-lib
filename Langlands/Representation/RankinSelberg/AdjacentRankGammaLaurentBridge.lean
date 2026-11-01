import Langlands.Representation.RankinSelberg.TwoBlockSmallFunctionalEquationLaurentBridge
import Langlands.Representation.RankinSelberg.AdjacentRankClearedContinuation
import Langlands.Representation.RankinSelberg.RationalGammaComparison
import Langlands.Representation.RankinSelberg.RationalMonomialFunctionalEquation

/-! Gamma equations after retaining an actual finite Laurent clearing kernel. -/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentGammaContinuation

open HarmonicAnalysis HarmonicAnalysis.BilateralLaurentSeries
open BilateralSpectralEvaluation TwoBlockFirstBlockLaurent LocalFactor

/-- A spectral expansion with absolute convergence on a right half-plane. -/
def HasAbsoluteBilateralSpectralExpansion
    (q : ℕ) (a : BilateralLaurentSeries) (I : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, C < s.re →
    Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s)

theorem HasAbsoluteBilateralSpectralExpansion.to_spectral
    {q : ℕ} {a : BilateralLaurentSeries} {I : ℂ → ℂ}
    (h : HasAbsoluteBilateralSpectralExpansion q a I) :
    HasBilateralSpectralExpansion q a I := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun s hs => (hC s hs).2⟩

/-- Spectral uniqueness applies to any finite Laurent clearing kernel. -/
theorem laurent_cleared_series_eq
    {q : ℕ} (hq : 1 < q) {K L : LaurentPolynomial ℂ}
    {I : ℂ → ℂ} {R : RationalFunctions}
    (hL : laurentToRatFunc L = laurentToRatFunc K * R)
    (hR : HasRationalContinuation q I R)
    {a : BilateralLaurentSeries}
    (ha : HasAbsoluteBilateralSpectralExpansion q a I) :
    K • a = ofLaurentPolynomial L := by
  obtain ⟨Ca, ha⟩ := ha
  obtain ⟨Cr, hR⟩ := hR
  apply bilateralSpectralCoefficientUniqueness q hq
  refine ⟨max Ca Cr, ?_⟩
  intro s hs
  have hsa := ha s ((le_max_left Ca Cr).trans_lt hs)
  have hsr := hR s ((le_max_right Ca Cr).trans_lt hs)
  let x : ℂˣ := spectralUnit (Nat.zero_lt_one.trans hq) s
  refine ⟨absolutelySummableAt_laurent_smul x K a hsa.1,
    absolutelySummableAt_ofLaurentPolynomial x L, ?_⟩
  calc
    (∑' k : ℤ, (K • a) k * spectralPoint q s ^ k) =
        laurentEval x K * I s :=
      (hasSum_laurent_smul x K a (I s) hsa.2).tsum_eq
    _ = laurentEval x L := by
      rw [hsr.2, ← eval_laurentToRatFunc x K, ← eval_laurentToRatFunc x L, hL]
      exact (RationalEvaluation.eval_mul (laurentToRatFunc_regular x K) hsr.1).symm
    _ = ∑' k : ℤ, ofLaurentPolynomial L k * spectralPoint q s ^ k :=
      (hasSum_ofLaurentPolynomial x L).tsum_eq.symm

/-- A finite Laurent-cleared expansion identifies the cleared rational value.
This direction only needs convergence of the original expansion. -/
theorem laurent_cleared_rational_identity
    {q : ℕ} (hq : 1 < q) {K L : LaurentPolynomial ℂ}
    {I : ℂ → ℂ} {R : RationalFunctions} {a : BilateralLaurentSeries}
    (ha : HasBilateralSpectralExpansion q a I)
    (hclear : K • a = ofLaurentPolynomial L)
    (hR : HasRationalContinuation q I R) :
    laurentToRatFunc L = laurentToRatFunc K * R := by
  obtain ⟨C, hC⟩ := ha
  have hL : HasRationalContinuation q
      (fun s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) K * I s)
      (laurentToRatFunc L) := by
    refine ⟨C, fun s hs => ?_⟩
    let x := spectralUnit (Nat.zero_lt_one.trans hq) s
    have hsum := hasSum_laurent_smul x K a (I s) (hC s hs)
    have hfinite := hasSum_ofLaurentPolynomial x L
    rw [← hclear] at hfinite
    have he : laurentEval x L = laurentEval x K * I s := hfinite.unique hsum
    exact ⟨laurentToRatFunc_regular x L,
      he.symm.trans (eval_laurentToRatFunc x L).symm⟩
  have hK : HasRationalContinuation q
      (fun s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) K)
      (laurentToRatFunc K) := by
    exact ⟨0, fun s _ =>
      ⟨laurentToRatFunc_regular (spectralUnit (Nat.zero_lt_one.trans hq) s) K,
        (eval_laurentToRatFunc (spectralUnit (Nat.zero_lt_one.trans hq) s) K).symm⟩⟩
  exact hL.unique hq (hK.mul hR)

/-- The finite reflection is involutive. -/
@[simp] theorem reflectLaurent_involutive {q : ℕ} (hq : 0 < q)
    (P : LaurentPolynomial ℂ) :
    reflectLaurent q hq (reflectLaurent q hq P) = P := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T k c =>
    rw [reflectLaurent_monomial, reflectLaurent_monomial]
    simp only [neg_neg, mul_assoc, ← zpow_add₀ hq0, neg_add_cancel,
      zpow_zero, mul_one]

/-- The coefficient reflection is involutive, without support restrictions. -/
@[simp] theorem reflectSeries_involutive {q : ℕ} (hq : 0 < q)
    (a : BilateralLaurentSeries) :
    reflectSeries q (reflectSeries q a) = a := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext n
  simp only [reflectSeries_apply, neg_neg, ← mul_assoc, ← zpow_add₀ hq0,
    add_neg_cancel, zpow_zero, one_mul]

/-- Finite Laurent reflection agrees with reciprocal rational substitution. -/
theorem laurentToRatFunc_reflectLaurent {q : ℕ} (hq : 0 < q)
    (P : LaurentPolynomial ℂ) :
    laurentToRatFunc (reflectLaurent q hq P) =
      RationalReflection.subst (spectralReflectionUnit hq) (laurentToRatFunc P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T k c =>
    rw [reflectLaurent_monomial]
    have hsC : ∀ c : ℂ, RationalReflection.subst (spectralReflectionUnit hq)
        (RatFunc.C c) = RatFunc.C c :=
      fun c => (RationalReflection.subst (spectralReflectionUnit hq)).commutes c
    simp only [map_mul, map_zpow₀, laurentToRatFunc_C, laurentToRatFunc_T,
      hsC, RationalReflection.subst_X, RationalReflection.reflectedVariable,
      RatFunc.algebraMap_eq_C, coe_spectralReflectionUnit]
    simp only [div_eq_mul_inv, map_inv₀, mul_zpow, inv_zpow, zpow_neg, mul_assoc]

/-- Clear the gamma equation while retaining the original clearing kernel.
The dual series is cleared on its own right half-plane by the reflected kernel;
no cancellation takes place in the module of bilateral series. -/
theorem gammaFE_cleared_coefficient_identity
    {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {G R Rd : RationalFunctions} {I Id : ℂ → ℂ}
    {a ad : BilateralLaurentSeries} {A B K L : LaurentPolynomial ℂ}
    (hG : laurentToRatFunc A = laurentToRatFunc B * G)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q Id Rd)
    (ha : HasAbsoluteBilateralSpectralExpansion q a I)
    (had : HasAbsoluteBilateralSpectralExpansion q ad Id)
    (hclear : K • a = ofLaurentPolynomial L)
    (hFE : GammaFunctionalEquation q ζ e G R Rd) :
    (B * K) • reflectSeries q ad =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e) * A * K) • a := by
  let hqpos := Nat.zero_lt_one.trans hq
  let E : LaurentPolynomial ℂ := LaurentPolynomial.C ((ζ : ℂ) ^ e) * A * L
  have hL := laurent_cleared_rational_identity hq ha.to_spectral hclear hR
  have hrat := GammaNormalization.rational_identity_of_gammaFunctionalEquation hq
    (coe_spectralReflectionUnit hqpos) hFE
  have hE : laurentToRatFunc E =
      laurentToRatFunc (B * K) *
        RationalReflection.subst (spectralReflectionUnit hqpos) Rd := by
    dsimp only [E]
    rw [map_mul, map_mul, laurentToRatFunc_C, map_mul, hL, hG, hrat]
    ring
  have hEd : laurentToRatFunc (reflectLaurent q hqpos E) =
      laurentToRatFunc (reflectLaurent q hqpos (B * K)) * Rd := by
    rw [laurentToRatFunc_reflectLaurent, hE, map_mul,
      RationalReflection.subst_subst, ← laurentToRatFunc_reflectLaurent]
  have hdual := laurent_cleared_series_eq hq hEd hRd had
  have href := congrArg (reflectSeries q) hdual
  rw [reflectSeries_laurent_smul q hqpos, reflectLaurent_involutive hqpos,
    reflectSeries_ofLaurentPolynomial q hqpos, reflectLaurent_involutive hqpos] at href
  rw [href]
  dsimp only [E]
  rw [ofLaurentPolynomial_mul, ← hclear, ← mul_smul]

/-- A retained-kernel coefficient identity recovers the gamma equation by
cancelling only in the rational-function field. The original cleared series
must be finite, and both original and dual expansions converge separately. -/
theorem gammaFE_of_cleared_coefficient_identity
    {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {G R Rd : RationalFunctions} {I Id : ℂ → ℂ}
    {a ad : BilateralLaurentSeries} {A B K L : LaurentPolynomial ℂ}
    (hB : B ≠ 0) (hK : K ≠ 0)
    (hG : laurentToRatFunc A = laurentToRatFunc B * G)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q Id Rd)
    (ha : HasBilateralSpectralExpansion q a I)
    (had : HasBilateralSpectralExpansion q ad Id)
    (hclear : K • a = ofLaurentPolynomial L)
    (hcoeff : (B * K) • reflectSeries q ad =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e) * A * K) • a) :
    GammaFunctionalEquation q ζ e G R Rd := by
  let hqpos := Nat.zero_lt_one.trans hq
  let E : LaurentPolynomial ℂ := LaurentPolynomial.C ((ζ : ℂ) ^ e) * A * L
  have hL := laurent_cleared_rational_identity hq ha hclear hR
  have hcoef' : (B * K) • reflectSeries q ad = ofLaurentPolynomial E := by
    rw [hcoeff]
    dsimp only [E]
    rw [ofLaurentPolynomial_mul, ← hclear, ← mul_smul]
  have href := congrArg (reflectSeries q) hcoef'
  rw [reflectSeries_laurent_smul q hqpos, reflectSeries_involutive hqpos,
    reflectSeries_ofLaurentPolynomial q hqpos] at href
  have hdual := laurent_cleared_rational_identity hq had href hRd
  have hrat := congrArg (RationalReflection.subst (spectralReflectionUnit hqpos)) hdual
  rw [laurentToRatFunc_reflectLaurent hqpos E, RationalReflection.subst_subst,
    map_mul (RationalReflection.subst (spectralReflectionUnit hqpos)),
    laurentToRatFunc_reflectLaurent hqpos (B * K),
    RationalReflection.subst_subst] at hrat
  have hBK : laurentToRatFunc (B * K) ≠ 0 := by
    exact fun hz => mul_ne_zero hB hK (laurentToRatFunc_injective (hz.trans (map_zero _).symm))
  have hidentity :
      RationalReflection.subst (spectralReflectionUnit hqpos) Rd =
        RatFunc.C ((ζ : ℂ) ^ e) * (G * R) := by
    apply mul_left_cancel₀ hBK
    rw [← hrat]
    dsimp only [E]
    rw [map_mul, map_mul, laurentToRatFunc_C, hL, hG, map_mul]
    ring
  exact RationalGammaComparison.gammaFunctionalEquation_of_rational_identity hq
    (coe_spectralReflectionUnit hqpos) hidentity

end Langlands.RankinSelberg.AdjacentGammaContinuation
