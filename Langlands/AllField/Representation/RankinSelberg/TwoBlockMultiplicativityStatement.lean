import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Two-block multiplicativity of the factors of pairs

The two-block cases of JPSS 1983, Theorem (3.1)(i)-(ii), printed pages 404-405.
These are the published multiplicativity targets with the number of blocks
fixed to two. Section (3.2), printed page 405, motivates isolating these cases.
The source uses lower induction; the targets use actual canonical normalized
upper induction. The required reversal, conjugation and factor transport are
future proof obligations. This module only states the two analytic targets.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockGammaMultiplicativityStatement TwoBlockLFactorMultiplicativityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- JPSS Theorem (3.1)(i) with two blocks: certified gamma factors for each
block pair exist and their product certifies the actual normalized induced pair.
This is `GammaMultiplicativityStatement` with `k` fixed to `2`. -/
def TwoBlockGammaMultiplicativityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- JPSS Theorem (3.1)(ii) with two blocks: certified L-polynomials exist for
the induced pair and both block pairs, with `X^e * ∏ i, Pi i = Q * P`.
This is `LFactorMultiplicativityStatement` with `k` fixed to `2`. -/
def TwoBlockLFactorMultiplicativityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

end Langlands.AllField.RankinSelberg
