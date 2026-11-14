import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistGammaStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.GeneralLinear

universe uF uV uW

/-- Twisting either member by the supplied determinant power shifts the complete
symmetric rational gamma factor by the actual spectral substitution. -/
def UnramifiedTwistGammaStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (u : ℂ) (χ : Fˣ →* ℂˣ),
    (∀ x : Fˣ,
      (χ x : ℂ) = (((⟨⟩ : LocalFieldData F).normalizedAbs (x : F) : ℝ) : ℂ) ^ u) →
    ∀ G : RationalFunctions, IsPadicSymmetricGammaFactor F ψ ν.val π σ G →
      IsPadicSymmetricGammaFactor F ψ ν.val π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G)

end Langlands.AllField.RankinSelberg
