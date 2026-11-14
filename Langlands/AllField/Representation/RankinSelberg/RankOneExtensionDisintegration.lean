import Langlands.Representation.RankinSelberg.RankOneExtensionDisintegration
import Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData
/-!
# Lower-block disintegration at the rank of the rank-one extension

The published lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]` from
`N_(t+1) \ GL_(t+1) × M_(1×(t+1)) × B⁻_1` to `N_(t+2) \ GL_(t+2)`, with its target rank
written as `(1 + t) + 1`, and the specialization of `LowerBlockQuotientDisintegrationStatement`
to this chart (JPSS §9.3, printed 456, in the rank used by Lemma (5.5)).
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LowerBlockQuotientDisintegrationStatement QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_lowerBlockQuotientDensity isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk measurable_lowerBlockQuotientDensity normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionDisintegration_of_statement rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.InducedTailIntermediate
open scoped ENNReal

universe uF

section Chart


end Chart

section Disintegration

private theorem quotientMeasureRankCast_symm {F : Type uF} [Field F]
    [TopologicalSpace F] {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F)))) :
    quotientMeasureRankCast h.symm (quotientMeasureRankCast h μ) = μ := by
  subst n
  rfl

private theorem unipotentHaar_rightInvariant_of_index_eq
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] {m n : ℕ} (h : m = n) :
    letI := borel (upperUnipotent (m + 1) F)
    letI : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    Measure.IsMulRightInvariant (unipotentHaar F m) →
      Measure.IsMulRightInvariant (unipotentHaar F n) := by
  subst n
  exact id

/-- `LowerBlockQuotientDisintegrationStatement` at `n = t`, `k = 0`, with the target rank
`t + 1 + 0 + 1` moved to `(1 + t) + 1`. The compatible measures, the additive Haar input
and the positive scalar are those of the statement. -/
theorem rankOneExtensionDisintegration_of_statement
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (t : ℕ) :
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup 1 F)
    letI : BorelSpace (lowerTriangularSubgroup 1 F) := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F)
      [Measure.IsMulRightInvariant (unipotentHaar F t)]
      [Measure.IsMulRightInvariant (unipotentHaar F (1 + t))]
      (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F)),
      IsCompatible (upperUnipotent (t + 1) F)
        (generalLinearHaar F t) (unipotentHaar F t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F)
        (generalLinearHaar F (1 + t)) (unipotentHaar F (1 + t)) μind →
      ∃ ρ : Measure (lowerTriangularSubgroup 1 F),
        ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧
        IsFiniteMeasureOnCompacts ρ ∧ ρ.IsMulRightInvariant ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ f : LeftUnipotentQuotient (1 + t) F → ℂ, Measurable f →
            (Integrable f μind ↔
              Integrable (f ∘ rankOneExtensionQuotientChart)
                ((μbase.withDensity
                  (lowerBlockQuotientDensity (⟨⟩ : LocalFieldData F) (t + 1) 1)).prod
                    ((rectangularMeasure η 1 (t + 1)).prod ρ))) ∧
            (Integrable f μind →
              ∫ q, f q ∂μind =
                (C : ℂ) * ∫ z, f (rankOneExtensionQuotientChart z)
                  ∂(μbase.withDensity
                    (lowerBlockQuotientDensity (⟨⟩ : LocalFieldData F) (t + 1) 1)).prod
                      ((rectangularMeasure η 1 (t + 1)).prod ρ)) := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F)
  let : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F)
  let : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
  let : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent ((1 + t) + 1) F)
  let : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (1 + t) F)
  let : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup 1 F)
  let : BorelSpace (lowerTriangularSubgroup 1 F) := ⟨rfl⟩
  intro η hrightBase hrightInd μbase μind hbase hind
  have hi : t + 1 + 0 = 1 + t := by omega
  let := borel (Langlands.GeneralLinear (t + 1 + 0 + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (t + 1 + 0 + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1 + 0 + 1) F)
  let : BorelSpace (upperUnipotent (t + 1 + 0 + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (t + 1 + 0) F)
  let : BorelSpace (LeftUnipotentQuotient (t + 1 + 0) F) := ⟨rfl⟩
  let : Measure.IsMulRightInvariant (unipotentHaar F (t + 1 + 0)) :=
    unipotentHaar_rightInvariant_of_index_eq hi.symm hrightInd
  let μraw := quotientMeasureRankCast (congrArg (· + 1) hi.symm) μind
  have hraw : IsCompatible (upperUnipotent (t + 1 + 0 + 1) F)
      (generalLinearHaar F (t + 1 + 0))
      (unipotentHaar F (t + 1 + 0)) μraw :=
    (compatible_quotientMeasureRankCast_iff hi.symm μind).2 hind
  rcases hdis F t 0 η μbase μraw hbase hraw with
    ⟨_, _, _, _, ρ, hreg, hσ, hpos, hfc, hright, _, C, hC, _, htransfer⟩
  refine ⟨ρ, hreg, hσ, hpos, hfc, hright, C, hC, fun f hf => ?_⟩
  let hr := congrArg (· + 1) hi
  let fraw := f ∘ upperUnipotentQuotientCongr hr
  have hfraw : Measurable fraw :=
    (measurable_comp_upperUnipotentQuotientCongr hr f).2 hf
  obtain ⟨hiff, hint⟩ := htransfer fraw hfraw
  have hμ : quotientMeasureRankCast hr μraw = μind :=
    quotientMeasureRankCast_symm (congrArg (· + 1) hi.symm) μind
  have hifull : Integrable f μind ↔ Integrable fraw μraw := by
    simpa only [hμ] using integrable_quotientMeasureRankCast_iff hr μraw f
  have hifullIntegral : ∫ q, f q ∂μind = ∫ q, fraw q ∂μraw := by
    simpa only [hμ, fraw, Function.comp_def] using
      integral_quotientMeasureRankCast hr μraw f
  exact ⟨hifull.trans hiff, fun hfi => hifullIntegral.trans (hint (hifull.mp hfi))⟩

end Disintegration

end Langlands.AllField.RankinSelberg
