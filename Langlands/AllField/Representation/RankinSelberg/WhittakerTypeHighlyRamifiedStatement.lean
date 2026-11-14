import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Highly ramified L-vanishing for pairs of Whittaker type

JPSS 1983, Proposition 2.13 (printed page 404), in the Whittaker-type scope
of Section 2.1. This proposition definition includes reducible representations
and both rank orders. The conclusion certifies the polynomial `1` in the
existing symmetric pair relation, including its compatible-measure existence
and universal measure quantifiers. No proof of the proposition is supplied.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeHighlyRamifiedLVanishingStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- JPSS 1983, Proposition 2.13: for any two representations of Whittaker type
of positive ranks, sufficiently ramified determinant twists of the first have
L-factor `1` against the second. The bound is uniform over all continuous
quasicharacters whose multiplicative conductor is at least that bound.
The supplied self-dual measure and additive character are arbitrary. -/
def WhittakerTypeHighlyRamifiedLVanishingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ),
    ∀ (r t : ℕ),
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (IsOfWhittakerType t (standardCharacter ψ t) σ) →
    ∃ A : ℕ, ∀ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1

end Langlands.AllField.RankinSelberg
