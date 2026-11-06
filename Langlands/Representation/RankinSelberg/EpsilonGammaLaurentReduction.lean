import Langlands.Representation.RankinSelberg.UnequalRankGammaFactor

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration
open LocalFactor

universe uF uV uW

/-- Every rational value in the family comes from a Laurent polynomial. -/
def HasLaurentValues (values : Set RationalFunctions) : Prop :=
  ∀ R ∈ values, ∃ L : LaurentCoefficients, laurentToRatFunc L = R

/-- A reciprocal-polynomial generator puts one in the Laurent span of its
values, by multiplying the reciprocal by the polynomial itself. -/
theorem IsNormalizedGenerator.one_mem_zetaSpan
    {values : Set RationalFunctions} {P : ℂ[X]} (h : IsNormalizedGenerator values P) :
    (1 : RationalFunctions) ∈ zetaSpan values := by
  have hrec : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [h.2]
    exact Submodule.mem_span_singleton_self _
  have hmul := (zetaSpan values).smul_mem P.toLaurent hrec
  simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_toLaurent,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero h.polynomial_ne_zero)] using hmul

/-- One is the normalized polynomial precisely when the values are Laurent
polynomials and their span contains one. -/
theorem isNormalizedGenerator_one_iff (values : Set RationalFunctions) :
    IsNormalizedGenerator values (1 : ℂ[X]) ↔
      HasLaurentValues values ∧ (1 : RationalFunctions) ∈ zetaSpan values := by
  rw [isNormalizedGenerator_iff]
  simp only [HasLaurentValues, Polynomial.coeff_one_zero, map_one, one_mul,
    inv_one, true_and]

/-- Laurent-valuedness forces an existing normalized reciprocal generator to
be the unit polynomial. No separate constant integral witness is needed. -/
theorem IsNormalizedGenerator.eq_one_of_laurentValues
    {values : Set RationalFunctions} {P : ℂ[X]} (h : IsNormalizedGenerator values P)
    (hL : HasLaurentValues values) : P = 1 :=
  h.unique ((isNormalizedGenerator_one_iff values).mpr ⟨hL, h.one_mem_zetaSpan⟩)

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

/-- Laurent values in block zero of the original and inverse-transpose pairs
force both common polynomials in the epsilon equation to equal one. -/
theorem UnequalRankEpsilonEquation.gammaEquation_of_laurentValues (hq : 1 < q)
    {c : ℂˣ} {m : ℤ}
    (hL : HasLaurentValues (unequalRankValuesAt 0 (r - n - 1) (by omega) q ψ abv μ
      (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ'))
    (hLd : HasLaurentValues (unequalRankValuesAt 0 (r - n - 1) (by omega) q
      (ψ.scale (-1)) abv μ (rectangularMeasure ν 0 (n + 1))
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')))
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m) :
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ'
      (rationalEpsilonMonomial c m : RationalFunctions) := by
  obtain ⟨ζ, P, Pd, hζ, hall⟩ := h
  have hP : P = 1 := (hall 0 (r - n - 1) (by omega)).1.eq_one_of_laurentValues hL
  have hPdgen := (hall (r - n - 1) 0 (by omega)).2.1
  rw [dualUnequalRankRationalValuesAt_eq] at hPdgen
  have hPd : Pd = 1 := hPdgen.eq_one_of_laurentValues hLd
  subst P Pd
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hG := UnequalRankEpsilonEquation.gammaEquation hq
    (δ := WeilDeligne.reflectionScale (q : ℝ) hq0) (by simp)
    (fun j k hr => (hall j k hr).1) (fun j k hr => (hall j k hr).2.1)
    ⟨ζ, 1, 1, hζ, hall⟩
  simpa only [rationalGammaExpression, map_one, mul_one, div_one] using hG

end Equation

section Universal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- Laurent-valued block-zero continuations for the pair and its dual turn
a universal epsilon certificate into the gamma certificate of its monomial. -/
theorem IsUnequalRankEpsilonFactor.gammaFactor_of_laurentValues (hnr : n < r) (hq : 1 < q)
    (hL : ∀ (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        HasLaurentValues (unequalRankValuesAt 0 (r - n - 1) (by omega) q ψ abv μ
          (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ'))
    (hLd : ∀ (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        HasLaurentValues (unequalRankValuesAt 0 (r - n - 1) (by omega) q
          (ψ.scale (-1)) abv μ (rectangularMeasure ν 0 (n + 1))
          (inverseTransposePullback π) (inverseTransposePullback σ)
          (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')))
    {e : ℂˣ × ℤ} (hε : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e) :
    IsUnequalRankGammaFactor hnr q ψ abv ν π σ
      (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) := by
  obtain ⟨hμex, hℓex, hℓ'ex, hall⟩ := hε
  refine ⟨hμex, hℓex, hℓ'ex, ?_⟩
  intro hinv μ hμ ℓ ℓ' hℓ hℓ'
  exact (hall μ hμ ℓ ℓ' hℓ hℓ').gammaEquation_of_laurentValues hq
    (hL μ hμ ℓ ℓ' hℓ hℓ') (hLd μ hμ ℓ ℓ' hℓ hℓ')

end Universal

end Langlands.RankinSelberg
