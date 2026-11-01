import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentReflection
import Langlands.Representation.RankinSelberg.BilateralSpectralEvaluation
import Langlands.Representation.RankinSelberg.BilateralSpectralCoefficientUniquenessStatement
import Langlands.Representation.RankinSelberg.BilateralSpectralCoefficientUniquenessProof

/-!
# From convergent small-block equations to cleared Laurent coefficients

The consumer lemmas use the published spectral uniqueness proof.
The earlier lemmas with an explicit uniqueness input remain available.
Each series is cleared on its own right half-plane before finite reflection.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open HarmonicAnalysis
open HarmonicAnalysis.BilateralLaurentSeries
open BilateralSpectralEvaluation

/-- The finite Laurent lift of an actual rational value cleared by its supplied
normalized generator. Its image under `laurentToRatFunc` determines it uniquely. -/
def normalizedGeneratorLaurentLift
    {P : Polynomial ℂ} {vals : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P)
    {R : RationalFunctions} (hRm : R ∈ vals) : LaurentPolynomial ℂ :=
  Classical.choose (hP.clearsDenominators (mem_zetaSpan hRm))

theorem normalizedGeneratorLaurentLift_spec
    {P : Polynomial ℂ} {vals : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P)
    {R : RationalFunctions} (hRm : R ∈ vals) :
    laurentToRatFunc (normalizedGeneratorLaurentLift hP hRm) =
      algebraMap (Polynomial ℂ) RationalFunctions P * R :=
  Classical.choose_spec (hP.clearsDenominators (mem_zetaSpan hRm))

theorem normalizedGeneratorLaurentLift_unique
    {P : Polynomial ℂ} {vals : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P)
    {R : RationalFunctions} (hRm : R ∈ vals) {L : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R) :
    normalizedGeneratorLaurentLift hP hRm = L :=
  laurentToRatFunc_injective ((normalizedGeneratorLaurentLift_spec hP hRm).trans hL.symm)

/-- A rationally cleared spectral series is the embedded finite Laurent lift,
provided the scalar spectral uniqueness proposition holds. -/
theorem cleared_series_eq_of_spectral_uniqueness
    (hunique : BilateralSpectralCoefficientUniquenessStatement)
    {q : ℕ} (hq : 1 < q) {P : Polynomial ℂ}
    {I : ℂ → ℂ} {R : RationalFunctions} {L : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R)
    (hR : HasRationalContinuation q I R)
    {a : BilateralLaurentSeries}
    (ha : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s)) :
    P.toLaurent • a = ofLaurentPolynomial L := by
  obtain ⟨Ca, ha⟩ := ha
  obtain ⟨Cr, hR⟩ := hR
  apply hunique q hq
  refine ⟨max Ca Cr, ?_⟩
  intro s hs
  have hsa := ha s ((le_max_left Ca Cr).trans_lt hs)
  have hsr := hR s ((le_max_right Ca Cr).trans_lt hs)
  let x : ℂˣ := spectralUnit (Nat.zero_lt_one.trans hq) s
  refine ⟨?_, ?_, ?_⟩
  · exact absolutelySummableAt_laurent_smul x P.toLaurent a hsa.1
  · exact absolutelySummableAt_ofLaurentPolynomial x L
  · calc
      (∑' k : ℤ, (P.toLaurent • a) k * spectralPoint q s ^ k) =
          laurentEval x P.toLaurent * I s :=
        (hasSum_laurent_smul x P.toLaurent a (I s) hsa.2).tsum_eq
      _ = laurentEval x L := by
        rw [laurentEval_toLaurent, hsr.2]
        exact (laurentEval_eq_of_laurentToRatFunc_eq x hL hsr.1).symm
      _ = ∑' k : ℤ, ofLaurentPolynomial L k * spectralPoint q s ^ k :=
        (hasSum_ofLaurentPolynomial x L).tsum_eq.symm

/-- The actual normalized generator supplies the finite Laurent lift needed
by scalar spectral uniqueness. -/
theorem normalizedGenerator_cleared_series
    (hunique : BilateralSpectralCoefficientUniquenessStatement)
    {q : ℕ} (hq : 1 < q) {P : Polynomial ℂ} {vals : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P)
    {I : ℂ → ℂ} {R : RationalFunctions} (hRm : R ∈ vals)
    (hR : HasRationalContinuation q I R)
    {a : BilateralLaurentSeries}
    (ha : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s)) :
    ∃ L : LaurentPolynomial ℂ,
      laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R ∧
      P.toLaurent • a = ofLaurentPolynomial L := by
  have hL := normalizedGeneratorLaurentLift_spec hP hRm
  exact ⟨normalizedGeneratorLaurentLift hP hRm, hL,
    cleared_series_eq_of_spectral_uniqueness hunique hq hL hR ha⟩

/-- Conditional analytic-to-coefficient bridge with the exact small functional
equation, actual normalized generators, and separate convergent expansions. -/
theorem smallFE_coefficient_identity_of_spectral_uniqueness
    (hunique : BilateralSpectralCoefficientUniquenessStatement)
    {q : ℕ} (hq : 1 < q) {P Pdual : Polynomial ℂ}
    {ζ c : ℂˣ} {e : ℕ} {d : ℤ} {vals valsD : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P) (hPd : IsNormalizedGenerator valsD Pdual)
    {I Id : ℂ → ℂ} {R Rd : RationalFunctions}
    (hRm : R ∈ vals) (hRdm : Rd ∈ valsD)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q Id Rd)
    (hFE : NormalizedFunctionalEquation q P Pdual ζ c e d R Rd)
    {a a' : BilateralLaurentSeries}
    (ha : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s))
    (ha' : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a' k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a' k * spectralPoint q s ^ k) (Id s)) :
    reflectedPolynomial q Pdual • reflectSeries q a' =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e * (c : ℂ)) *
        LaurentPolynomial.T d * P.toLaurent) • a := by
  obtain ⟨L, hL, hclear⟩ :=
    normalizedGenerator_cleared_series hunique hq hP hRm hR ha
  obtain ⟨Ld, hLd, hcleard⟩ :=
    normalizedGenerator_cleared_series hunique hq hPd hRdm hRd ha'
  exact normalizedFE_coefficient_identity_of_cleared hq hL hLd hFE a a' hclear hcleard

/-- A rationally cleared spectral series is the embedded finite Laurent lift,
using the published scalar spectral uniqueness theorem. -/
theorem cleared_series_eq
    {q : ℕ} (hq : 1 < q) {P : Polynomial ℂ}
    {I : ℂ → ℂ} {R : RationalFunctions} {L : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R)
    (hR : HasRationalContinuation q I R)
    {a : BilateralLaurentSeries}
    (ha : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s)) :
    P.toLaurent • a = ofLaurentPolynomial L :=
  cleared_series_eq_of_spectral_uniqueness
    bilateralSpectralCoefficientUniqueness hq hL hR ha

/-- Analytic-to-coefficient bridge with the exact small functional equation,
actual normalized generators, and separate convergent expansions. -/
theorem smallFE_coefficient_identity
    {q : ℕ} (hq : 1 < q) {P Pdual : Polynomial ℂ}
    {ζ c : ℂˣ} {e : ℕ} {d : ℤ} {vals valsD : Set RationalFunctions}
    (hP : IsNormalizedGenerator vals P) (hPd : IsNormalizedGenerator valsD Pdual)
    {I Id : ℂ → ℂ} {R Rd : RationalFunctions}
    (hRm : R ∈ vals) (hRdm : Rd ∈ valsD)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q Id Rd)
    (hFE : NormalizedFunctionalEquation q P Pdual ζ c e d R Rd)
    {a a' : BilateralLaurentSeries}
    (ha : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a k * spectralPoint q s ^ k) (I s))
    (ha' : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Summable (fun k : ℤ => ‖a' k * spectralPoint q s ^ k‖) ∧
      HasSum (fun k : ℤ => a' k * spectralPoint q s ^ k) (Id s)) :
    reflectedPolynomial q Pdual • reflectSeries q a' =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e * (c : ℂ)) *
        LaurentPolynomial.T d * P.toLaurent) • a :=
  smallFE_coefficient_identity_of_spectral_uniqueness
    bilateralSpectralCoefficientUniqueness hq hP hPd hRm hRdm hR hRd hFE ha ha'

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
