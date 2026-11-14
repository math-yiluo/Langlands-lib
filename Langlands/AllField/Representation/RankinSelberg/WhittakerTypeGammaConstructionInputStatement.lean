import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputStatement
import Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType
/-! Canonical symmetric gamma construction inputs from the original Whittaker types.
This module defines a proposition; it does not prove the analytic or functional
equation results needed to establish it. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeGammaConstructionInputStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

/-- The existing canonical symmetric construction input follows from standard
Whittaker type of both original representations, at any supplied self-dual measure.
This is a closed statement of the derived JPSS consequence, not its proof. -/
def WhittakerTypeGammaConstructionInputStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType n (standardCharacter ψ n) σ →
    PadicSymmetricGammaConstructionInput F ψ ν.val π σ

end Langlands.AllField.RankinSelberg
