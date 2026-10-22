import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.UnipotentQuotient

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration
open LocalFactor

universe uF uV uW

section FixedRank

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The existing block analytic conclusion, transporting only the equality of
natural-number dimensions so that the larger rank is fixed independently. -/
def UnequalRankAnalyticAt (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) : Prop := by
  subst r
  exact UnequalRankAnalyticConclusion j k q ψ abv μ ν π σ ℓ ℓ'

/-- The published intrinsic/model generator comparison with the large rank fixed. -/
theorem UnequalRankAnalyticAt.isNormalizedGenerator_iff
    (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)}
    {ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (P : ℂ[X]) :
    IsNormalizedGenerator (unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ) P ↔
      IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ') P := by
  subst r
  exact h.isUnequalRankLPolynomial_iff hπ hσ hℓ hℓ' P

end FixedRank

section Equation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ} {hnr : n < r}

/-- The epsilon equation with its common normalized polynomials yields the
gamma equation for every block on the full reduced-denominator domain. -/
theorem UnequalRankEpsilonEquation.gammaEquation (hq : 1 < q)
    {δ c : ℂˣ} {m : ℤ} {P Pdual : ℂ[X]} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hP : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ
        (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ') P)
    (hPd : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ') Pdual)
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m) :
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ'
      (rationalGammaExpression δ c m P Pdual) := by
  obtain ⟨ζ, P₀, Pd₀, hζ, hall⟩ := h
  have hr0 : r = n + (0 + (r - n - 1) + 1) := by omega
  obtain rfl := (hall 0 (r - n - 1) hr0).1.unique (hP 0 (r - n - 1) hr0)
  obtain rfl := (hall 0 (r - n - 1) hr0).2.1.unique (hPd 0 (r - n - 1) hr0)
  refine ⟨ζ, hζ, ?_⟩
  intro j k hr
  refine ⟨(hP j k hr).exists_ne_zero, ?_⟩
  intro f f'
  obtain ⟨R, Rd, hR, hRd, hN⟩ := (hall j k hr).2.2 f f'
  exact ⟨R, Rd, hR, hRd,
    hN.gamma_value_of_regular hq hδ (hPd j k hr).polynomial_ne_zero⟩

end Equation

section Universal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

variable (hnr : n < r)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
  (hπd : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
    (inverseTransposePullback π))
  (hσd : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
    (inverseTransposePullback σ))
  (hA : ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 → ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankAnalyticAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')
  (hAd : ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 → ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankAnalyticAt j k hr q (ψ.scale (-1)) abv μ
        (rectangularMeasure ν j (n + 1))
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))

include hnr hπ hσ hπd hσd hA hAd

/-- Intrinsic polynomials and the uniform epsilon relation give the universal
unequal-rank gamma relation, including every complementary block. -/
theorem IsUnequalRankEpsilonFactor.gammaFactor (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (hε : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hPd : IsDualPairLPolynomial q ψ abv μ ν π σ Pdual) :
    IsUnequalRankGammaFactor hnr q ψ abv ν π σ
      (rationalGammaExpression δ e.1 e.2 P Pdual) := by
  obtain ⟨hμex, hℓex, hℓ'ex, hall⟩ := hε
  refine ⟨hμex, hℓex, hℓ'ex, ?_⟩
  intro hinv μ' hμ' ℓ ℓ' hℓ hℓ'
  have hmeas : μ' = μ := (unipotentQuotientHaar_unique F n μ' hμ').trans
    (unipotentQuotientHaar_unique F n μ hμ).symm
  subst μ'
  apply UnequalRankEpsilonEquation.gammaEquation hq hδ
  · intro j k hr
    exact (UnequalRankAnalyticAt.isNormalizedGenerator_iff j k hr
      (hA ℓ ℓ' hℓ hℓ' j k hr) hπ hσ hℓ hℓ' P).mp
      ((isPairLPolynomial_of_lt hnr).mp hP j k hr)
  · intro j k hr
    rw [dualUnequalRankRationalValuesAt_eq]
    exact (UnequalRankAnalyticAt.isNormalizedGenerator_iff k j (by omega)
      (hAd ℓ ℓ' hℓ hℓ' k j (by omega)) hπd hσd
      (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') Pdual).mp
      ((isPairLPolynomial_of_lt hnr).mp hPd k j (by omega))
  · exact @hall hinv μ hμ ℓ ℓ' hℓ hℓ'

variable [BorelSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The existing gamma unit satisfies the universal relation in unequal ranks
under explicit original and dual analytic hypotheses for all blocks. -/
theorem pairGammaFactor_isPairGammaFactor_unequalRank (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ) :
    IsPairGammaFactor q ψ abv ν π σ
      (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) := by
  rw [pairGammaFactor_eq_expression hq hν hμ hε hL hdual
    (pairEpsilonData_spec hε) (pairLPolynomial_spec hL) (pairLPolynomial_spec hdual),
    isPairGammaFactor_of_lt hnr]
  exact IsUnequalRankEpsilonFactor.gammaFactor hnr hπ hσ hπd hσd hA hAd hq (by simp) hμ
    ((isPairEpsilonFactor_of_lt hnr).mp (pairEpsilonData_spec hε))
    (pairLPolynomial_spec hL) (pairLPolynomial_spec hdual)

omit [BorelSpace (LeftUnipotentQuotient n F)] [BorelSpace F] [T2Space F]
  [TotallyDisconnectedSpace F] in
/-- The common polynomials furnished by the epsilon equation generate every
intrinsic original and dual block family under the explicit analytic inputs. -/
theorem unequalRank_pairLPolynomialsExist
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    PairLPolynomialExists q ψ abv μ ν π σ ∧
      DualPairLPolynomialExists q ψ abv μ ν π σ := by
  obtain ⟨e, he⟩ := hε
  obtain ⟨-, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := (isPairEpsilonFactor_of_lt hnr).mp he
  obtain ⟨ζ, P, Pd, -, hFE⟩ := hall μ hμ ℓ ℓ' hℓ hℓ'
  constructor
  · refine ⟨P, (isPairLPolynomial_of_lt hnr).mpr ?_⟩
    intro j k hr
    exact (UnequalRankAnalyticAt.isNormalizedGenerator_iff j k hr
      (hA ℓ ℓ' hℓ hℓ' j k hr) hπ hσ hℓ hℓ' P).mpr (hFE j k hr).1
  · refine ⟨Pd, (isPairLPolynomial_of_lt hnr).mpr ?_⟩
    intro j k hr
    apply (UnequalRankAnalyticAt.isNormalizedGenerator_iff j k hr
      (hAd ℓ ℓ' hℓ hℓ' j k hr) hπd hσd
      (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') Pd).mpr
    have hPd := (hFE k j (by omega)).2.1
    rwa [dualUnequalRankRationalValuesAt_eq] at hPd

/-- Unequal-rank gamma as an actual unit with the universal JPSS relation.
Common intrinsic L-polynomials are derived from the uniform epsilon equation. -/
def unequalRankGammaFactor (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    {G : RationalFunctionsˣ // IsPairGammaFactor q ψ abv ν π σ (G : RationalFunctions)} :=
  let hL := unequalRank_pairLPolynomialsExist hnr hπ hσ hπd hσd hA hAd hμ hε
  ⟨pairGammaFactor hq hν hμ hε hL.1 hL.2,
    pairGammaFactor_isPairGammaFactor_unequalRank hnr hπ hσ hπd hσd hA hAd
      hq hν hμ hε hL.1 hL.2⟩

end Universal

end Langlands.RankinSelberg
