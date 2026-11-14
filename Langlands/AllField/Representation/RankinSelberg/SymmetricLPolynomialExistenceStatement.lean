import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Existence of symmetric p-adic L-polynomials

A closed statement for actual representations of Whittaker type in either rank
order, using the canonical p-adic data and a supplied self-dual Haar measure.
This packages JPSS Theorem 2.7(ii) with the rank convention in Section 2.12.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

/-- Every pair of Whittaker-type representations has a symmetric p-adic
L-polynomial, common to all compatible quotient measures. This is a proposition
definition, not a proof of the analytic existence theorem. -/
def SymmetricLPolynomialExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (IsOfWhittakerType n (standardCharacter ψ n) σ) →
    ∃ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P

end Langlands.AllField.RankinSelberg
