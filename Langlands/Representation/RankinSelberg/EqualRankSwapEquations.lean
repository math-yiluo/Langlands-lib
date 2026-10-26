import Langlands.Representation.RankinSelberg.EqualRankSwapIntegrals
import Langlands.Representation.RankinSelberg.GammaFactor

/-! Direct transport of the fixed-character functional equations. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory Polynomial

universe uF uV uW

section RationalAlgebra

/-- Multiplying by a nonzero constant creates and removes no poles. -/
theorem denom_eval_const_mul_ne_zero_iff (c : ℂ) (hc : c ≠ 0)
    (R : RationalFunctions) (x : ℂ) :
    (RatFunc.C c * R).denom.eval x ≠ 0 ↔ R.denom.eval x ≠ 0 := by
  have hcancel : RatFunc.C c⁻¹ * (RatFunc.C c * R) = R := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  constructor
  · intro hnew hold
    have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c⁻¹) (RatFunc.C c * R)
    rw [hcancel, RatFunc.denom_C, one_mul] at hdvd
    exact hnew (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hold)
  · intro hold hnew
    have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c) R
    rw [RatFunc.denom_C, one_mul] at hdvd
    exact hold (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hnew)

/-- The product of scalar powers converts the old second-model sign to the
new second-model sign. -/
theorem minusOne_swap_scalar (α β : ℂˣ) (hβ : β ^ 2 = 1) (e : ℕ) :
    ((α : ℂ) ^ e * (β : ℂ) ^ e) * (β : ℂ) ^ e = (α : ℂ) ^ e := by
  have hβC : (β : ℂ) * (β : ℂ) = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using
      congrArg Units.val hβ
  rw [mul_assoc, ← mul_pow, hβC, one_pow, mul_one]

/-- Transport a normalized equation on its full denominator domain. -/
theorem NormalizedFunctionalEquation.negOne_swap
    {q e : ℕ} {P Pdual : ℂ[X]} {α β c : ℂˣ} {m : ℤ}
    {R Rdual : RationalFunctions} (hβ : β ^ 2 = 1)
    (h : NormalizedFunctionalEquation q P Pdual β c e m R Rdual) :
    NormalizedFunctionalEquation q P Pdual α c e m R
      (RatFunc.C ((α : ℂ) ^ e * (β : ℂ) ^ e) * Rdual) := by
  let κ : ℂ := (α : ℂ) ^ e * (β : ℂ) ^ e
  have hκ : κ ≠ 0 := mul_ne_zero (pow_ne_zero _ α.ne_zero) (pow_ne_zero _ β.ne_zero)
  intro s hR hnew
  have hd : Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0 :=
    (denom_eval_const_mul_ne_zero_iff κ hκ Rdual _).mp hnew
  have hC : Polynomial.eval₂ (RingHom.id ℂ) (spectralPoint q (1 - s))
      (RatFunc.C κ).denom ≠ 0 := by
    rw [RatFunc.denom_C, Polynomial.eval₂_one]
    exact one_ne_zero
  rw [RatFunc.eval_mul (RingHom.id ℂ) (spectralPoint q (1 - s))
      hC hd, RatFunc.eval_C]
  calc
    Pdual.eval (spectralPoint q (1 - s)) * (κ * Rdual.eval _ _) =
        κ * (Pdual.eval (spectralPoint q (1 - s)) * Rdual.eval _ _) := by ring
    _ = κ * ((β : ℂ) ^ e * epsilonMonomial q c m s *
        (P.eval (spectralPoint q s) * R.eval _ _)) := by rw [h s hR hd]
    _ = (κ * (β : ℂ) ^ e) * epsilonMonomial q c m s *
        (P.eval (spectralPoint q s) * R.eval _ _) := by ring
    _ = (α : ℂ) ^ e * epsilonMonomial q c m s *
        (P.eval (spectralPoint q s) * R.eval _ _) := by
      rw [minusOne_swap_scalar α β hβ]

/-- The same scalar conversion transports the gamma equation directly. -/
theorem GammaFunctionalEquation.negOne_swap
    {q e : ℕ} {α β : ℂˣ} {G R Rdual : RationalFunctions} (hβ : β ^ 2 = 1)
    (h : GammaFunctionalEquation q β e G R Rdual) :
    GammaFunctionalEquation q α e G R
      (RatFunc.C ((α : ℂ) ^ e * (β : ℂ) ^ e) * Rdual) := by
  let κ : ℂ := (α : ℂ) ^ e * (β : ℂ) ^ e
  have hκ : κ ≠ 0 := mul_ne_zero (pow_ne_zero _ α.ne_zero) (pow_ne_zero _ β.ne_zero)
  intro s hR hnew hG
  have hd : Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0 :=
    (denom_eval_const_mul_ne_zero_iff κ hκ Rdual _).mp hnew
  have hC : Polynomial.eval₂ (RingHom.id ℂ) (spectralPoint q (1 - s))
      (RatFunc.C κ).denom ≠ 0 := by
    rw [RatFunc.denom_C, Polynomial.eval₂_one]
    exact one_ne_zero
  rw [RatFunc.eval_mul (RingHom.id ℂ) (spectralPoint q (1 - s))
      hC hd, RatFunc.eval_C, h s hR hd hG]
  calc
    κ * ((β : ℂ) ^ e * (G.eval _ _ * R.eval _ _)) =
        (κ * (β : ℂ) ^ e) * (G.eval _ _ * R.eval _ _) := by ring
    _ = (α : ℂ) ^ e * (G.eval _ _ * R.eval _ _) := by
      rw [minusOne_swap_scalar α β hβ]

end RationalAlgebra

section CoefficientEquations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  [BorelSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  (hμ : HasCharacterChangeMeasureLaw abv (-1) μ) (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

include hμ

/-- Transport the epsilon equation, keeping the original Fourier pair and
both normalized polynomials. -/
theorem EqualRankEpsilonEquation.negOne_swap
    {q : ℕ} {α c : ℂˣ} {m : ℤ}
    (hα : HasModelMinusOneScalar π ℓ α) (hℓ' : ℓ'.val ≠ 0)
    (h : EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m) :
    EqualRankEpsilonEquation q ψ abv μ ν σ π
      (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ) c m := by
  obtain ⟨β, P, Pdual, hβ, hP, hPdual, hall⟩ := h
  refine ⟨α, P, Pdual, HasModelMinusOneScalar.negOneInverse ψ π hα, ?_, ?_, ?_⟩
  · rwa [equalRankRationalValues_negOne_swap ψ abv μ hμ π σ ℓ ℓ' q]
  · exact (isNormalizedGenerator_congr
      (zetaSpan_dualEqualRankRationalValues_negOne_swap ψ abv μ hμ π σ ℓ ℓ' q hα hβ)
      Pdual).mpr hPdual
  · intro g g' Φ
    obtain ⟨f', rfl⟩ := negOneStandardModelVector_surjective ψ σ ℓ' g
    obtain ⟨f, rfl⟩ := negOneInverseModelVector_surjective ψ π ℓ g'
    obtain ⟨Φhat, R, Rdual, hFourier, hR, hRdual, hFE⟩ := hall f f' Φ
    exact ⟨Φhat, R, RatFunc.C ((α : ℂ) ^ n * (β : ℂ) ^ n) * Rdual, hFourier,
      hasRationalContinuation_equalRank_negOne_swap ψ abv μ hμ π σ ℓ ℓ' f f' Φ hR,
      hasRationalContinuation_dualEqualRank_negOne_swap ψ abv μ hμ π σ ℓ ℓ'
        hα hβ f f' Φhat hRdual,
      NormalizedFunctionalEquation.negOne_swap (hβ.sq_eq_one hℓ') hFE⟩

/-- Transport the gamma equation directly, retaining the same gamma rational
function and Fourier pair. -/
theorem EqualRankGammaEquation.negOne_swap
    {q : ℕ} {α : ℂˣ} {G : RationalFunctions}
    (hα : HasModelMinusOneScalar π ℓ α) (hℓ' : ℓ'.val ≠ 0)
    (h : EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G) :
    EqualRankGammaEquation q ψ abv μ ν σ π
      (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ) G := by
  obtain ⟨β, hβ, hnonzero, hall⟩ := h
  refine ⟨α, HasModelMinusOneScalar.negOneInverse ψ π hα, ?_, ?_⟩
  · rwa [equalRankRationalValues_negOne_swap ψ abv μ hμ π σ ℓ ℓ' q]
  · intro g g' Φ
    obtain ⟨f', rfl⟩ := negOneStandardModelVector_surjective ψ σ ℓ' g
    obtain ⟨f, rfl⟩ := negOneInverseModelVector_surjective ψ π ℓ g'
    obtain ⟨Φhat, R, Rdual, hFourier, hR, hRdual, hFE⟩ := hall f f' Φ
    exact ⟨Φhat, R, RatFunc.C ((α : ℂ) ^ n * (β : ℂ) ^ n) * Rdual, hFourier,
      hasRationalContinuation_equalRank_negOne_swap ψ abv μ hμ π σ ℓ ℓ' f f' Φ hR,
      hasRationalContinuation_dualEqualRank_negOne_swap ψ abv μ hμ π σ ℓ ℓ'
        hα hβ f f' Φhat hRdual,
      GammaFunctionalEquation.negOne_swap (hβ.sq_eq_one hℓ') hFE⟩

end CoefficientEquations

end Langlands.RankinSelberg
