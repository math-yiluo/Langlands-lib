import Langlands.Representation.RankinSelberg.TwoBlockDominantLaurentAlgebra
import Langlands.Representation.RankinSelberg.AdjacentRankClearedContinuation
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.GodementJacquet.GeometricDenominatorCancellation

/-!
# Rational consequences of the dominant-rank finite numerators

Actual convergent spectral sums connect finite coefficient clearing to rational
values. Neither the first-block equations nor their parameter continuation is
asserted by this internal algebraic and analytic assembly.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis LaurentPolynomial LocalFactor
open HarmonicAnalysis.BilateralLaurentSeries BilateralSpectralEvaluation

/-- The dominant finite reflection is the existing reciprocal Laurent
substitution with reciprocal scalar. -/
theorem laurentReflection_eq_reciprocal (q : ℂˣ) (A : LaurentPolynomial ℂ) :
    laurentReflection q A = GodementJacquet.laurentReciprocal q⁻¹ A := by
  have hpow (k : ℤ) :
      (↑(laurentMonomialUnit q⁻¹ (-1) ^ k) : LaurentPolynomial ℂ) =
        C ((q : ℂ) ^ (-k)) * T (-k) := by
    cases k with
    | ofNat n =>
      simp [laurentMonomialUnit, mul_pow, ← map_pow, T_pow]
    | negSucc n =>
      rw [Int.negSucc_eq, zpow_neg, ← inv_zpow, laurentMonomialUnit_inv]
      change (↑(laurentMonomialUnit q⁻¹⁻¹ (- -1) ^ (n + 1)) :
        LaurentPolynomial ℂ) = _
      simp [laurentMonomialUnit, mul_pow, ← map_pow, T_pow]
      left
      congr 1
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB => simp only [map_add, hA, hB]
  | C_mul_T k c =>
    rw [laurentReflection_C_mul_T]
    simp only [GodementJacquet.laurentReciprocal, map_mul,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, hpow]
    rw [mul_assoc]

/-- Actual reciprocal substitution commutes with the Laurent embedding in
rational functions. -/
theorem laurentToRatFunc_reflection (q : ℂˣ) (A : LaurentPolynomial ℂ) :
    laurentToRatFunc (laurentReflection q A) =
      RationalReflection.subst q⁻¹ (laurentToRatFunc A) := by
  rw [laurentReflection_eq_reciprocal,
    GodementJacquet.laurentToRatFunc_reciprocal]

/-- Extend the published polynomial-clearing evaluation bridge to an arbitrary
finite Laurent multiplier by clearing its negative powers first. -/
theorem clearedSpectralExpansion_laurentRationalIdentity
    {q : ℕ} (hq : 1 < q) (a : BilateralLaurentSeries) (f : ℂ → ℂ)
    (A Q : LaurentPolynomial ℂ) (R : RationalFunctions)
    (hexp : HasBilateralSpectralExpansion q a f)
    (hclear : ofLaurentPolynomial Q = A • a)
    (hR : HasRationalContinuation q f R) :
    laurentToRatFunc Q = laurentToRatFunc A * R := by
  obtain ⟨e, P, hP⟩ := LaurentPolynomial.exists_T_pow A
  have hclearP : ofLaurentPolynomial (Q * T (e : ℤ)) = P.toLaurent • a := by
    calc
      ofLaurentPolynomial (Q * T (e : ℤ)) =
          T (e : ℤ) • ofLaurentPolynomial Q := by
            rw [mul_comm Q, ofLaurentPolynomial_mul]
      _ = (T (e : ℤ) * A) • a := by rw [hclear, mul_smul]
      _ = P.toLaurent • a := by rw [mul_comm, ← hP]
  have h := clearedSpectralExpansion_rationalIdentity hq a f P
    (Q * T (e : ℤ)) R hexp hclearP hR
  rw [← laurentToRatFunc_toLaurent, hP, map_mul, map_mul] at h
  apply mul_right_cancel₀
    (show laurentToRatFunc (T (e : ℤ)) ≠ 0 by
      rw [laurentToRatFunc_T]
      exact zpow_ne_zero _ RatFunc.X_ne_zero)
  simpa only [mul_right_comm] using h

/-- A finite original numerator and its reflected dual numerator, with both
clearing factors and the specified Laurent unit retained. -/
def HasReflectedFiniteNumerators (q : ℂˣ)
    (a aD : BilateralLaurentSeries) (A B : LaurentPolynomial ℂ)
    (M : (LaurentPolynomial ℂ)ˣ) : Prop :=
  ∃ N : LaurentPolynomial ℂ,
    ofLaurentPolynomial N = A • a ∧
    ofLaurentPolynomial (laurentReflection q N) =
      (laurentReflection q (↑(M⁻¹) : LaurentPolynomial ℂ) * B) • aD

/-- Paired finite numerators give the rational whole-pair identity, retaining
both polynomial clearing factors and removing only the specified unit. The
two scalar expansions may converge on different right half-planes. -/
theorem reflectedNumerators_rationalIdentity
    {q : ℕ} (hq : 1 < q) (qU : ℂˣ)
    {a aD : BilateralLaurentSeries} {f fD : ℂ → ℂ}
    (A B : LaurentPolynomial ℂ) (M : (LaurentPolynomial ℂ)ˣ)
    (R RD : RationalFunctions)
    (hexp : HasBilateralSpectralExpansion q a f)
    (hexpD : HasBilateralSpectralExpansion q aD fD)
    (hnum : HasReflectedFiniteNumerators qU a aD A B M)
    (hR : HasRationalContinuation q f R)
    (hRD : HasRationalContinuation q fD RD) :
    RationalReflection.subst qU⁻¹ (laurentToRatFunc B * RD) =
      laurentToRatFunc (M : LaurentPolynomial ℂ) * laurentToRatFunc A * R := by
  obtain ⟨N, hN, hND⟩ := hnum
  have hOriginal := clearedSpectralExpansion_laurentRationalIdentity
    hq a f A N R hexp hN hR
  have hDual := clearedSpectralExpansion_laurentRationalIdentity
    hq aD fD _ _ RD hexpD hND hRD
  rw [laurentToRatFunc_reflection, map_mul, laurentToRatFunc_reflection] at hDual
  have h := congrArg (RationalReflection.subst qU⁻¹) hDual
  simp only [map_mul, RationalReflection.subst_subst] at h
  have hUnit : laurentToRatFunc (M : LaurentPolynomial ℂ) *
      laurentToRatFunc (↑(M⁻¹) : LaurentPolynomial ℂ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc
    RationalReflection.subst qU⁻¹ (laurentToRatFunc B * RD) =
        (laurentToRatFunc (M : LaurentPolynomial ℂ) *
          laurentToRatFunc (↑(M⁻¹) : LaurentPolynomial ℂ)) *
            RationalReflection.subst qU⁻¹ (laurentToRatFunc B * RD) := by
              rw [hUnit, one_mul]
    _ = laurentToRatFunc (M : LaurentPolynomial ℂ) * laurentToRatFunc N := by
      simpa only [map_mul, mul_assoc] using
        congrArg (fun z => laurentToRatFunc (M : LaurentPolynomial ℂ) * z) h.symm
    _ = _ := by rw [hOriginal, mul_assoc]

/-- Uniform finite clearing bounds a normalized generator with exactly the
polynomial direction required by the dominant L target. -/
theorem normalizedGenerator_divisibility_of_clearedExpansions
    {q : ℕ} (hq : 1 < q) (S : Set RationalFunctions)
    (P A : Polynomial ℂ) (hP : IsNormalizedGenerator S P) (hA : A ≠ 0)
    (hclear : ∀ R ∈ S, ∃ (a : BilateralLaurentSeries) (f : ℂ → ℂ),
      HasBilateralSpectralExpansion q a f ∧
      HasRationalContinuation q f R ∧
      ∃ N : LaurentPolynomial ℂ, ofLaurentPolynomial N = A.toLaurent • a) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  have hspan : zetaSpan S ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply Submodule.span_le.mpr
    intro R hR
    obtain ⟨a, f, hexp, hcont, hN⟩ := hclear R hR
    exact clearedSpectralExpansion_mem_reciprocalSpan hq a f A hA R hexp hN hcont
  apply (reciprocalLaurentSpanClearing P A hP.polynomial_ne_zero hA).mp
  apply hspan
  rw [hP.2]
  exact Submodule.subset_span rfl

end Langlands.RankinSelberg.DominantRankTransport
