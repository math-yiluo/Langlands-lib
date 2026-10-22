import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.UnipotentQuotient

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration
open LocalFactor

universe uF uV uW

section Equation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- Fixed-functional epsilon equations yield gamma equations after matching both
normalized generators. The reduced-denominator domain includes canceled zeros. -/
theorem EqualRankEpsilonEquation.gammaEquation (hq : 1 < q)
    {δ c : ℂˣ} {m : ℤ} {P Pdual : ℂ[X]} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (hPd : IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pdual)
    (h : EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m) :
    EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ'
      (rationalGammaExpression δ c m P Pdual) := by
  obtain ⟨ζ, P₀, Pd₀, hζ, hP₀, hPd₀, hFE⟩ := h
  obtain rfl := hP₀.unique hP
  obtain rfl := hPd₀.unique hPd
  refine ⟨ζ, hζ, hP.exists_ne_zero, ?_⟩
  intro f f' Φ
  obtain ⟨Φhat, R, Rd, hΦ, hR, hRd, hN⟩ := hFE f f' Φ
  refine ⟨Φhat, R, Rd, hΦ, hR, hRd, ?_⟩
  exact hN.gamma_value_of_regular hq hδ hPd.polynomial_ne_zero

end Equation

section Universal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

variable (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
  (hπd : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n)
    (inverseTransposePullback π))
  (hσd : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
    (inverseTransposePullback σ))
  (hA : ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 → EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
  (hAd : ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))

include hπ hσ hπd hσd hA hAd

/-- The intrinsic original and dual L-polynomials produce the universal gamma
relation. Uniqueness of the normalized quotient measure discharges its measure
quantifier; the two analytic conclusions match the actual model families. -/
theorem IsEqualRankEpsilonFactor.gammaFactor (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (hε : IsEqualRankEpsilonFactor q ψ abv ν π σ e)
    (hP : IsEqualRankLPolynomial q ψ abv μ π σ P)
    (hPd : IsEqualRankLPolynomial q (ψ.scale (-1)) abv μ
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual) :
    IsEqualRankGammaFactor q ψ abv ν π σ (rationalGammaExpression δ e.1 e.2 P Pdual) := by
  obtain ⟨hμex, hℓex, hℓ'ex, hall⟩ := hε
  refine ⟨hμex, hℓex, hℓ'ex, ?_⟩
  intro hinv μ' hμ' ℓ ℓ' hℓ hℓ'
  have hmeas : μ' = μ := (unipotentQuotientHaar_unique F n μ' hμ').trans
    (unipotentQuotientHaar_unique F n μ hμ).symm
  subst μ'
  apply EqualRankEpsilonEquation.gammaEquation hq hδ
    (((hA ℓ ℓ' hℓ hℓ').isEqualRankLPolynomial_iff hπ hσ hℓ hℓ' P).mp hP)
    ((dualEqualRank_isLPolynomial_iff q ψ abv μ π σ ℓ ℓ' hπd hσd hℓ hℓ'
      (hAd ℓ ℓ' hℓ hℓ') Pdual).mp hPd)
  exact @hall hinv μ hμ ℓ ℓ' hℓ hℓ'

variable [BorelSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The previously constructed pair gamma unit satisfies the published universal
relation in equal rank, under explicit original and dual analytic hypotheses. -/
theorem pairGammaFactor_isPairGammaFactor_equalRank (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ) :
    IsPairGammaFactor q ψ abv ν π σ
      (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) := by
  rw [pairGammaFactor_eq_expression hq hν hμ hε hL hdual
    (pairEpsilonData_spec hε) (pairLPolynomial_spec hL) (pairLPolynomial_spec hdual),
    isPairGammaFactor_self]
  exact IsEqualRankEpsilonFactor.gammaFactor hπ hσ hπd hσd hA hAd hq (by simp) hμ
    (isPairEpsilonFactor_self.mp (pairEpsilonData_spec hε))
    (isPairLPolynomial_self.mp (pairLPolynomial_spec hL))
    (isPairLPolynomial_self.mp (pairLPolynomial_spec hdual))

omit [BorelSpace (LeftUnipotentQuotient n F)] [BorelSpace F] [T2Space F]
  [TotallyDisconnectedSpace F] in
/-- The epsilon relation supplies nonzero functionals, and the two analytic
conclusions give intrinsic original and dual L-polynomial existence. -/
theorem equalRank_pairLPolynomialsExist
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    PairLPolynomialExists q ψ abv μ ν π σ ∧
      DualPairLPolynomialExists q ψ abv μ ν π σ := by
  obtain ⟨e, he⟩ := hε
  obtain ⟨-, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, -⟩ := isPairEpsilonFactor_self.mp he
  obtain ⟨P, hP⟩ := (hA ℓ ℓ' hℓ hℓ').normalizedGeneratorExists hπ hσ hℓ hℓ'
  obtain ⟨Pd, hPd⟩ := (hAd ℓ ℓ' hℓ hℓ').normalizedGeneratorExists hπd hσd
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
  exact ⟨⟨P, isPairLPolynomial_self.mpr hP⟩, ⟨Pd, isPairLPolynomial_self.mpr hPd⟩⟩

/-- Equal-rank gamma as an actual unit equipped with its universal JPSS relation.
Intrinsic L-polynomial existence is derived from the analytic inputs; epsilon
existence and original/dual analytic conclusions remain explicit hypotheses. -/
def equalRankGammaFactor (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    {G : RationalFunctionsˣ // IsPairGammaFactor q ψ abv ν π σ (G : RationalFunctions)} :=
  let hL := equalRank_pairLPolynomialsExist hπ hσ hπd hσd hA hAd hε
  ⟨pairGammaFactor hq hν hμ hε hL.1 hL.2,
    pairGammaFactor_isPairGammaFactor_equalRank hπ hσ hπd hσd hA hAd hq hν hμ hε hL.1 hL.2⟩

end Universal

end Langlands.RankinSelberg
