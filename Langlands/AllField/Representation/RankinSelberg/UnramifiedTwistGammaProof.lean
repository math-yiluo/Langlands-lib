import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof
import Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement
import Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistGammaStatement
/-! # Complete symmetric unramified gamma spectral transport -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistGammaStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply unramifiedTwistGamma
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis

universe uF uV uW

namespace UnramifiedGammaTwist
open Langlands.RankinSelberg.UnramifiedGammaTwist hiding padic_pair_both padic_symmetric_both
open Langlands.AllField.RankinSelberg.UnramifiedGammaTwist
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistGammaStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply unramifiedTwistGamma
open Langlands.AllField.RankinSelberg

section PairTransport


end PairTransport

section PadicTransport

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : letI := borel F
    AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (u : ℂ) (χ : Fˣ →* ℂˣ)
  (hχ : ∀ x : Fˣ,
    (χ x : ℂ) = ((⟨⟩ : LocalFieldData F).normalizedAbs (x : F) : ℂ) ^ u)

include hχ in
/-- The canonical p-adic specialization keeps the field's actual residue
cardinality, normalized absolute value, additive character and Haar measure. -/
theorem padic_pair_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsPadicPairGammaFactor F ψ ν π σ G) :
    IsPadicPairGammaFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G) ∧
      IsPadicPairGammaFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G) := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  exact pair_both (⟨⟩ : LocalFieldData F).residueCardinality
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) ν u χ hχ π σ h

include hχ in
/-- Reading the larger rank first covers either rank order and exchanges the
two twist positions in the reversed branch. -/
theorem padic_symmetric_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsPadicSymmetricGammaFactor F ψ ν π σ G) :
    IsPadicSymmetricGammaFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G) ∧
      IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit (⟨⟩ : LocalFieldData F).residueCardinality
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u) G) := by
  unfold IsPadicSymmetricGammaFactor at h ⊢
  split_ifs at h ⊢ with hnr
  · exact padic_pair_both F ψ ν u χ hχ π σ h
  · exact (padic_pair_both F ψ ν u χ hχ σ π h).symm

end PadicTransport

end UnramifiedGammaTwist

/-- Twisting either member by the supplied unramified determinant character
transports the complete symmetric gamma certificate by `X ↦ q^(-u) * X`. -/
theorem unramifiedTwistGamma : UnramifiedTwistGammaStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t V _ _ W _ _ π σ u χ hχ G h
  exact Langlands.AllField.RankinSelberg.UnramifiedGammaTwist.padic_symmetric_both F ψ ν.val u χ hχ π σ h

end Langlands.AllField.RankinSelberg
