import Langlands.Representation.RankinSelberg.TwoBlockLVerifiedInputAssembly
import Langlands.AllField.HarmonicAnalysis.UnboundedConductorProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLConditionalAssembly
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUniverseTransport
/-!
# Published inputs for the two-block L-polynomial descent

The available inputs are proved from imported Library theorems. The final
implication retains the three analytic bases, restricted reverse divisibility,
and high-ramification vanishing as explicit hypotheses.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLVerifiedInputAssembly
open Langlands.RankinSelberg.TwoBlockLVerifiedInputAssembly hiding AvailableInputs availableInputs equalRankReverseAt twoBlockLFactorMultiplicativity_of_remainingInputs
open Langlands.AllField.RankinSelberg.TwoBlockLVerifiedInputAssembly
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRankOneExtensionLDivisibilityStatement EqualRankRankOneExtensionSpanComparisonStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaMultiplicativityStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLFactorMultiplicativityStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement WhittakerTypeHighlyRamifiedLVanishingStatement ZeroRowLastRowCutoffStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankExtensionFamily equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRankOneExtensionLDivisibility equalRankRankOneExtensionSpanComparison equalRankRankOneExtensionSpanComparison_of equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSpanComparison_core equalRankUnitValue exists_inverseWhittaker_twoBlockExtension finiteFunctionMellin finiteFunctionShellSeries half_mul_determinantWeight hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_equalRankExtension isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_universeLift_iff isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_universeLift_iff iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionSpanComparison_of_pointwise rankOneExtensionWhittakerContraction rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists twoBlockGammaMultiplicativity_of_commonUniverse twoBlockLFactorMultiplicativity_of_commonUniverse unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicQuasicharacterUnboundedConductorStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicQuasicharacterUnboundedConductor padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis

universe uF uV uW u

/-- The endpoint's scalar lift is definitionally the lift in the conditional
descent, so the published closed endpoint supplies its fieldwise input. -/
theorem equalRankReverseAt (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ) :
    Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly.EqualRankReverseAt.{uF, uV, uW} F ψ ν :=
  equalRankRankOneExtensionLDivisibility.{uF, uV, uW} F ψ ν

/-- The seven inputs already supplied by closed Library proofs, in the
carrier universe used by both descending inductions. -/
def AvailableInputs : Prop :=
  (∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ),
    Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly.EqualRankReverseAt.{uF, max uF u, max uF u} F ψ ν) ∧
  SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u} ∧
  EqualRankFactorSwapStatement.{uF, max uF u, max uF u} ∧
  NormalizedProductWhittakerTypeStatement.{uF, max uF u} ∧
  RankOneWhittakerTypeStatement.{uF} ∧
  EqualRankFactorSwapStatement.{uF, 0, max uF u} ∧
  PadicQuasicharacterUnboundedConductorStatement.{uF}

/-- No analytic proposition is assumed in this package of available inputs. -/
theorem availableInputs : AvailableInputs.{uF, u} :=
  ⟨fun F _ _ _ _ ψ ν => equalRankReverseAt F ψ ν,
    symmetricLPolynomialExists.{uF, max uF u, max uF u},
    equalRankFactorSwap.{uF, max uF u, max uF u},
    normalizedProductWhittakerType.{uF, max uF u},
    rankOneWhittakerType.{uF},
    equalRankFactorSwap.{uF, 0, max uF u},
    padicQuasicharacterUnboundedConductor.{uF}⟩

/-- The remaining five analytic inputs suffice for the original target with
independent field, test-carrier, and block-carrier universes. -/
theorem twoBlockLFactorMultiplicativity_of_remainingInputs
    (hdominant :
      TwoBlockLDominantRankStatement.{uF, max uF uV uW, max uF uV uW})
    (hadjacent :
      TwoBlockLAdjacentRankStatement.{uF, max uF uV uW, max uF uV uW})
    (hrankBase :
      TwoBlockLRankOneStatement.{uF, max uF uV uW, max uF uV uW})
    (hrestricted :
      RankOneExtensionLDivisibilityStatement.{uF, max uF uV uW, max uF uV uW})
    (hram :
      WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF uV uW}) :
    TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW} := by
  obtain ⟨hequal, hexists, hswap, htype, hrankOne, hscalarSwap, hcharacters⟩ :=
    availableInputs.{uF, max uV uW}
  apply twoBlockLFactorMultiplicativity_of_commonUniverse.{uF, uV, uW}
  exact Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly.twoBlockLMultiplicativity_of_inputs_commonUniverse.{uF, max uV uW}
    hdominant hadjacent hrankBase hrestricted hequal hexists hswap htype hram
    hrankOne hscalarSwap hcharacters

end Langlands.AllField.RankinSelberg.TwoBlockLVerifiedInputAssembly
