import Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Equal-rank exchange of p-adic pair-factor certificates

JPSS (2.12) explicitly asserts equal-rank symmetry of L and epsilon factors.
Gamma symmetry is derived from the epsilon/L-ratio formula of (3.1)(2).
This module only defines the proposition; it does not prove or assume it.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

/-- Equal-rank exchange for the existing L-polynomial, epsilon and gamma
relations on actual representations of Whittaker type. Both original
Whittaker-type hypotheses use the standard character for the same `ψ`.
The proposition retains each relation's compatible-quotient-measure quantifiers
and does not assert that a factor exists. -/
def EqualRankFactorSwapStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    (IsOfWhittakerType n (standardCharacter ψ n) π) →
    (IsOfWhittakerType n (standardCharacter ψ n) σ) →
    (∀ P : ℂ[X],
      IsPadicPairLPolynomial F ψ ν.val π σ P ↔
        IsPadicPairLPolynomial F ψ ν.val σ π P) ∧
    (∀ e : ℂˣ × ℤ,
      IsPadicPairEpsilonFactor F ψ ν.val π σ e ↔
        IsPadicPairEpsilonFactor F ψ ν.val σ π e) ∧
    (∀ G : RationalFunctions,
      IsPadicPairGammaFactor F ψ ν.val π σ G ↔
        IsPadicPairGammaFactor F ψ ν.val σ π G)

end Langlands.AllField.RankinSelberg
