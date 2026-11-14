import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Multiplicativity of the factors of pairs

JPSS 1983, Theorem (3.1), printed pages 404-405: for `π` of Whittaker type on
`GL_r(F)` and `σ = Ind(σ_1, …, σ_p)` induced from representations of Whittaker
type on the blocks of a standard parabolic of `GL_t(F)`, the gamma factor of
`π × σ` is the product of the gamma factors of `π × σ_i`, and
`L(s, π × σ)` lies in `∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`. The factors are the
relations `IsPadicSymmetricGammaFactor` and `IsPadicSymmetricLPolynomial` with
the self-dual measure, which cover both rank orders. The induced
representation is the published normalized induction
`canonicalNormalizedProductInduced` from the standard upper block parabolic.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- JPSS 1983, Theorem (3.1)(i) (printed page 405). Let `π` be a representation
of Whittaker type of `GL_(r+1)(F)`, and `σ_1, …, σ_k` representations of
Whittaker type of `GL_(m_i + 1)(F)` with `∑ (m_i + 1) = t + 1`. Then each pair
`(π, σ_i)` has a gamma factor `G_i`, and their product is the gamma factor of
`π` against the normalized induction of `(σ_1, …, σ_k)` to `GL_(t+1)(F)`. -/
def GammaMultiplicativityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin k → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- JPSS 1983, Theorem (3.1)(ii) (printed page 405), with the hypotheses of
`GammaMultiplicativityStatement`: the L-polynomials `P` of `π` against the
induced representation and `P_i` of `(π, σ_i)` exist, and
`L(s, π × σ) ∈ ∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`, that is,
`X^e ∏ P_i = Q P` for a polynomial `Q` and some `e`. -/
def LFactorMultiplicativityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin k → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

end Langlands.AllField.RankinSelberg
