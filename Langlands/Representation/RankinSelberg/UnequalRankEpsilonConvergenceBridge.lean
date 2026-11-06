import Langlands.Representation.RankinSelberg.UnequalRankGammaFactor

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

/-- Absolute convergence on some right half-plane for each pair of functions
in the two specified coefficient models, with the larger rank fixed. -/
def UnequalRankConvergenceAt (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) : Prop := by
  subst r
  exact ∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∃ a : ℝ, ∀ s : ℂ, a < s.re → UnequalRankConverges ψ abv j k μ ν f.val f'.val s

/-- Multiplicity one and convergence suffice to compare intrinsic zeta values
with the rational continuations of a chosen pair of nonzero models. -/
theorem UnequalRankConvergenceAt.zetaValues_eq
    (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)}
    {ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankConvergenceAt j k hr ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ =
      unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ' := by
  subst r
  exact unequalRankZetaValues_eq_rationalValues q ψ abv j k μ ν hπ hσ hℓ hℓ' h

/-- The normalized-generator comparison needs convergence but does not need
separate rationality, common-denominator or generator-existence hypotheses. -/
theorem UnequalRankConvergenceAt.isNormalizedGenerator_iff
    (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)}
    {ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (h : UnequalRankConvergenceAt j k hr ψ abv μ ν π σ ℓ ℓ')
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (P : ℂ[X]) :
    IsNormalizedGenerator (unequalRankZetaValuesAt j k hr q ψ abv μ ν π σ) P ↔
      IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ') P := by
  rw [h.zetaValues_eq j k hr hπ hσ hℓ hℓ']

end FixedRank

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
  (hC : ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 → ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankConvergenceAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')
  (hCd : ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
    ℓ.val ≠ 0 → ℓ'.val ≠ 0 → ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankConvergenceAt j k hr (ψ.scale (-1)) abv μ
        (rectangularMeasure ν j (n + 1))
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))

include hnr hπ hσ hπd hσd hC hCd

/-- An epsilon certificate and intrinsic original/dual L-polynomials determine
the gamma relation using only the convergence portion of the analytic theorem. -/
theorem IsUnequalRankEpsilonFactor.gammaFactor_of_convergence (hq : 1 < q)
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
    exact (UnequalRankConvergenceAt.isNormalizedGenerator_iff j k hr
      (hC ℓ ℓ' hℓ hℓ' j k hr) hπ hσ hℓ hℓ' P).mp
      ((isPairLPolynomial_of_lt hnr).mp hP j k hr)
  · intro j k hr
    rw [dualUnequalRankRationalValuesAt_eq]
    exact (UnequalRankConvergenceAt.isNormalizedGenerator_iff k j (by omega)
      (hCd ℓ ℓ' hℓ hℓ' k j (by omega)) hπd hσd
      (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') Pdual).mp
      ((isPairLPolynomial_of_lt hnr).mp hPd k j (by omega))
  · exact @hall hinv μ hμ ℓ ℓ' hℓ hℓ'

/-- When both intrinsic L-polynomials are one, the epsilon monomial is itself
the ordered pair gamma factor, under explicit convergence hypotheses. -/
theorem IsPairEpsilonFactor.gammaFactor_of_convergence_of_L_eq_one (hq : 1 < q)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    {e : ℂˣ × ℤ} (hε : IsPairEpsilonFactor q ψ abv ν π σ e)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ 1)
    (hPd : IsDualPairLPolynomial q ψ abv μ ν π σ 1) :
    IsPairGammaFactor q ψ abv ν π σ (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) := by
  rw [isPairGammaFactor_of_lt hnr]
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have h := IsUnequalRankEpsilonFactor.gammaFactor_of_convergence hnr hπ hσ hπd hσd
    hC hCd hq (δ := WeilDeligne.reflectionScale (q : ℝ) hq0) (by simp) hμ
    ((isPairEpsilonFactor_of_lt hnr).mp hε) hP hPd
  simpa only [rationalGammaExpression, map_one, mul_one, div_one] using h

end Universal

end Langlands.RankinSelberg
