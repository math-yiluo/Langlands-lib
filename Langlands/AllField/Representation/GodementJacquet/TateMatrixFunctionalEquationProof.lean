import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationProof
import Langlands.AllField.Representation.GodementJacquet.TateMatrixAnalyticData
import Langlands.AllField.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.TateScalarFunctionalEquation
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar
/-! The rank-one matrix functional equation with its supplied Fourier measure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding MatrixUnitValueStatement TateMatrixFunctionalEquationStatement matrixUnitValue scalarMellinAnalyticData_finiteFunction tateMatrixFunctionalEquation
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries glCoefficientModel_isOfWhittakerType hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_prod_generalLinear_one_natWeight inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit matrixComparisonModelsTopology measurableSet_determinantSlice mem_determinantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV

section FourierTransport


end FourierTransport

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData exists_biSmoothCoefficient_ne_zero exists_matrixIntegral_one exists_tateCharacterCoefficient exists_tateIotaMatrixAnalyticAssertions exists_tateMatrixAnalyticAssertions exists_tateMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_tateScalarEquiv_iff integral_tateScalarEquiv iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues tateAnalyticsGLBorel tateAnalyticsGLMeasurable tateAnalyticsLocalField tateAnalyticsTopology tateAnalyticsUnitsBorel tateAnalyticsUnitsMeasurable tateAnalyticsValuation tateCharacterModelOne_at_one tateCharacter_mellinAnalyticData tateDualEqualRankIntegral_eq_scalar tateDualEqualRankIntegral_unit_eq_scalar tateDualEqualRankRationalValues_eq_scalar tateEqualRankIntegral_eq_scalar tateEqualRankIntegral_unit_eq_scalar tateEqualRankRationalValues_eq_scalar tateFEBorel tateFEGLBorel tateFEGLMeasurable tateFELocalField tateFEMeasurable tateFEQuotientBorel tateFEQuotientMeasurable tateFET2 tateFETopology tateFETotallyDisconnected tateFEUnipotentBorel tateFEUnipotentMeasurable tateFEUnitsBorel tateFEUnitsMeasurable tateFEValuativeRel tateHasShiftedRationalValue_iff tateIotaMatrixRationalValues_eq_scalar tateMatrixIntegral_eq_scalar tateMatrixIntegrand_eq_scalar tateMatrixRationalValues_eq_scalar tateMatrix_characterConverges tateProofBorel tateProofLocalField tateProofMeasurable tateProofT2 tateProofTopology tateProofTotallyDisconnected tateProofUnitsBorel tateProofUnitsMeasurable tateProofValuation tateScalarEquiv_measurePreserving tateScalarFunctionalEquation tateTransportGLBorel tateTransportGLLocallyCompact tateTransportGLMeasurable tateTransportGLSecondCountable tateTransportLocalField tateTransportTopology tateTransportUnitsBorel tateTransportUnitsMeasurable tateTransportValuation tateTrivialModelOne_at_one whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData TateMatrixFunctionalEquationStatement iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue scalarMellinAnalyticData_finiteFunction tateMatrixFunctionalEquation whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance tateProofT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance tateProofTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance tateProofMeasurable : MeasurableSpace F := borel _
local instance tateProofBorel : BorelSpace F := ⟨rfl⟩
local instance tateProofUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance tateProofUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]

/-- A proved scalar action on the actual carrier gives the full matrix data.
The Fourier witness is chosen before every coefficient and continuation. -/
theorem exists_tateMatrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hν : IsSelfDual ψ ν)
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a := by
  have hinv (x : Fˣ) : ((χ⁻¹) x : ℂ) = (χ x : ℂ)⁻¹ :=
    Units.val_inv_eq_inv_val (χ x)
  obtain ⟨P, hP⟩ := exists_tateMatrixAnalyticAssertions F σ χ hσ hact
  obtain ⟨PDual, hPDual⟩ := exists_tateIotaMatrixAnalyticAssertions F σ χ hσ hact
  have hPscalar : IsNormalizedGenerator
      (scalarMellinRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
        (⟨⟩ : LocalFieldData F).normalizedAbs (localMultiplicativeHaar F)
        (fun x => (χ x : ℂ)) 1) P := by
    have h := hP.2.2
    change IsNormalizedGenerator (matrixRationalValues F σ) P at h
    rwa [tateMatrixRationalValues_eq_scalar F σ χ hσ hact] at h
  have hPDualScalar : IsNormalizedGenerator
      (scalarMellinRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
        (⟨⟩ : LocalFieldData F).normalizedAbs (localMultiplicativeHaar F)
        (fun x => ((χ x)⁻¹ : ℂ)) 1) PDual := by
    have h := hPDual.2.2
    change IsNormalizedGenerator (iotaMatrixRationalValues F σ) PDual at h
    rw [tateIotaMatrixRationalValues_eq_scalar F σ χ hσ hact] at h
    simpa only [hinv] using h
  obtain ⟨c, a, hFE⟩ := tateScalarFunctionalEquation F ψ χ ν hν hPscalar hPDualScalar
  refine ⟨P, PDual, c, a, hP, hPDual, fun Φ => ?_⟩
  obtain ⟨φhat, hFourier, -⟩ := hFE (tateScalarTest F Φ)
  let Φhat : MatrixTestFunction 0 F :=
    Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F) φhat
  refine ⟨Φhat, tateMatrixFourierPair_of_scalar ψ ν Φ φhat hFourier, ?_⟩
  intro f R RDual hR hRDual
  obtain ⟨ψhat, hScaledFourier, hScaledFE⟩ :=
    hFE (f.val 1 • tateScalarTest F Φ)
  have hScaled : ψhat = f.val 1 • φhat :=
    tateScalarFourierWitness_smul ψ ν (tateScalarTest F Φ) φhat ψhat
      (f.val 1) (fun y => (hFourier y).2) (fun y => (hScaledFourier y).2)
  have hOriginal := (tateHasShiftedRationalValue_iff F χ f.val
    (tateCoefficient_eq σ χ hact f) Φ R).mp hR
  have hiota1 : coefficientIota f.val 1 = f.val 1 := by
    simp [coefficientIota]
  have hiota : ∀ g, coefficientIota f.val g =
      coefficientIota f.val 1 * ((χ⁻¹) (determinant g) : ℂ) := by
    intro g
    change f.val (inverseTranspose 1 F g) = _
    rw [hiota1, tateCoefficient_eq σ χ hact f,
      tateInverseTranspose_eq_inv, map_inv, map_inv]
    rfl
  have hDual := (tateHasShiftedRationalValue_iff F χ⁻¹ (coefficientIota f.val)
    hiota Φhat RDual).mp hRDual
  have hTest : tateScalarTest F Φhat = φhat :=
    (Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F)).left_inv φhat
  rw [hiota1, hTest] at hDual
  rw [hScaled] at hScaledFE
  exact hScaledFE R RDual hOriginal (by simpa only [hinv] using hDual)

end Padic

/-- Full rank-one Godement--Jacquet functional equation for the original
admissible irreducible representation and the supplied self-dual measure. -/
theorem tateMatrixFunctionalEquation : TateMatrixFunctionalEquationStatement.{uF,uV} := by
  intro F _ _ _ _ ψ ν hν V hV hModule σ ha hi
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  let : MeasurableSpace (Langlands.GeneralLinear 1 F) := borel _
  let : BorelSpace (Langlands.GeneralLinear 1 F) := ⟨rfl⟩
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Langlands.GeneralLinear 1 F)) σ.asModule
  obtain ⟨χ, ⟨e⟩⟩ := exists_tateCharacterModel σ ha hi
  have hact : TateCharacterAction σ χ := by
    intro g v
    apply e.injective
    rw [map_smul]
    have h := Representation.IntertwiningMap.isIntertwining σ
      (rankOneCharacter (χ : Fˣ →* ℂˣ)) e.toIntertwiningMap g v
    simpa [rankOneCharacter, characterRepresentation, twist] using h
  exact Langlands.AllField.GodementJacquet.Padic.exists_tateMatrixFunctionalEquationData F ψ ν hν σ χ ha.1 hact

end Langlands.AllField.GodementJacquet
