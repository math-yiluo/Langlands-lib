import Langlands.Representation.RankinSelberg.SubmodelGammaComparison
import Langlands.AllField.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonProof
import Langlands.AllField.Representation.Whittaker.ModelGenericSocleProof
/-!
# Gamma comparison for an actual subrepresentation of a coefficient model

The original representation can be reducible. An ambient matrix functional
equation supplies the specified gamma expression on a subrepresentation of its
coefficient model. Existence of a gamma certificate on the original remains a
separate premise.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicUnitTestStatement ModelGenericSocleStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelGenericSocle modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker

universe uG uV



end Langlands.AllField.Whittaker

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankUnitValueStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput PairedMatrixBlockComparison PrincipalDualAssertions QuotientHaarExistenceStatement RankOneAmbientMatrixFunctionalEquationComparisonStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RawModelIotaMatrixConvergence TorusCoefficientEnvelope UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement ambientComparisonGLBorel ambientComparisonGLMeasurable ambientComparisonLocalField ambientComparisonQuotientBorel ambientComparisonQuotientMeasurable ambientComparisonScalarBorel ambientComparisonScalarMeasurable ambientComparisonT2 ambientComparisonTopology ambientComparisonTotallyDisconnected ambientComparisonUnipotentBorel ambientComparisonUnipotentMeasurable ambientComparisonValuation ambientZeroGLBorel ambientZeroGLMeasurable ambientZeroLocalField ambientZeroQuotientBorel ambientZeroQuotientMeasurable ambientZeroScalarMeasurable ambientZeroTopology ambientZeroUnipotentBorel ambientZeroUnipotentMeasurable ambientZeroValuation biSmooth_matrixDiagonal_convergesOnRight boundedDiagonalNormIntegrand boundedDiagonalNormIntegrand_convergesOnRight boundedDiagonalNormIntegrand_le_matrixDiagonal boxDiagonalLocalField boxDiagonalTopology boxDiagonalUnitsBorel boxDiagonalUnitsMeasurable boxDiagonalValuativeRel boxLatticeTest_fourier_rightLeadingSign boxLatticeTest_rightLeadingSign coefficientModelEvaluation_coefficient compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantNorm_rankOneSignedWeyl determinantNorm_rankOneWeylLeadingSign determinantWeight_principalSignedBlockPoint diagonalBorelDensity diagonalConj_map diagonalSliceWeight diagonalSliceWeight_nonneg diagonal_abs_bound diagonal_abs_last dualFunction_blockMatrixAt_rankCast enorm_weightedCoefficient_sub_natCast equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support exists_uniform_matrixUnipotentNormSlice_bound gamma_eq_submodel gamma_of_submodel_ambient_matrix glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc hasEqualRankCompactTest_of_kirillov integrable_biSmooth_matrixDiagonalIntegrand integrable_diagonalUnits_of_principalFixed integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_principalFixedBlockIntegrand_signedDual_iff integrable_principalModelBlockIntegrand_of_fixed integrable_principalModelFourierIntegrand_signedDual_iff integrable_prod_generalLinear_one_natWeight_iff integrable_rankOneDualBlockIntegrand_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_principalFixedBlockIntegrand_signedDual integral_principalModelBlockIntegrand_of_fixed integral_principalModelFourierIntegrand_signedDual integral_prod_generalLinear_one_natWeight integral_rankOneDualBlockIntegrand isClopen_matrixNormBox isCompact_matrixNormBox isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit lintegral_iwasawa_diagonalBorelDensity lintegral_norm_matrixIntegrand_iwasawa matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation matrixConvergesOnRight_inverseTransposePullback matrixConvergesOnRight_of_torusEnvelope matrixDiagonalIntegrand matrixIntegrand_exists_principalFixed matrixNormBox matrixNormBoxTest matrixNormBoxTest_diagonal_of_le matrixUnipotentNormSlice measurable_biSmooth_matrixIntegrand measurable_boundedDiagonalNormIntegrand measure_diagonalUnits_preimage_principalLevel_le_one modelDataLocalField modelDataTopology modelDataValuativeRel normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType pairedComparisonGLBorel pairedComparisonGLMeasurable pairedComparisonLocalField pairedComparisonQuotientBorel pairedComparisonQuotientMeasurable pairedComparisonScalarMeasurable pairedComparisonTopology pairedComparisonUnipotentBorel pairedComparisonUnipotentMeasurable pairedComparisonValuativeRel parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalDualGLBorel principalDualGLMeasurable principalDualLocalField principalDualQuotientMeasurable principalDualScalarBorel principalDualScalarMeasurable principalDualT2 principalDualTopology principalDualTotallyDisconnected principalDualUnipotentBorel principalDualUnipotentMeasurable principalDualValuation principalDual_value principalFixedBlockIntegrand principalFixedBlockIntegrand_density principalFixedDualBorel principalFixedDualGLBorel principalFixedDualGLMeasurable principalFixedDualGLSecondCountable principalFixedDualLocalField principalFixedDualMeasurable principalFixedDualSecondCountable principalFixedDualT2 principalFixedDualTopology principalFixedDualTotallyDisconnected principalFixedDualValuativeRel principalFixedModelDual_pairing principalModelBlockIntegrand principalModelBlockIntegrand_ae_of_fixed principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalModelFourierIntegrand_signedDual_eq principalSignedBlockPoint rankOneAmbientMatrixFunctionalEquationComparison rankOneAmbientMatrixFunctionalEquationComparison_zero rankOneAmbientModelMatrixCoefficient rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneDualBlockIntegrand rankOneDualBlockIntegrand_eq_quotient rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneSignedDualHomeomorph rankOneSignedDualHomeomorph_apply rankOneSignedDualHomeomorph_preserving rankOneWhittakerType rankOne_blockZero_exists_ne_zero rawMatrixGLBorel rawMatrixGLMeasurable rawMatrixLocalField rawMatrixNBorel rawMatrixNMeasurable rawMatrixSecondCountable rawMatrixT2 rawMatrixTopology rawMatrixUnitsBorel rawMatrixUnitsMeasurable rawMatrixUnitsSecondCountable rawMatrixValuativeRel rawModelIotaMatrixConvergence_of_modelIota scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedDualBlockGLBorel signedDualBlockGLMeasurable signedDualBlockGLSigmaCompact signedDualBlockLocalField signedDualBlockQuotientBorel signedDualBlockQuotientMeasurable signedDualBlockScalarBorel signedDualBlockScalarMeasurable signedDualBlockSecondCountable signedDualBlockT2 signedDualBlockTopology signedDualBlockUnipotentBorel signedDualBlockUnipotentMeasurable signedDualBlockValuation signedDualTransportGLBorel signedDualTransportGLMeasurable signedDualTransportLocalField signedDualTransportScalarMeasurable signedDualTransportTopology signedDualTransportValuation signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real smoothDiagonalGLBorel smoothDiagonalGLLocallyCompact smoothDiagonalGLMeasurable smoothDiagonalGLSecondCountable smoothDiagonalLocalField smoothDiagonalSecondCountable smoothDiagonalT2 smoothDiagonalTopology smoothDiagonalUnitsBorel smoothDiagonalUnitsMeasurable smoothDiagonalUnitsSecondCountable smoothDiagonalValuativeRel smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel submodelComparisonBorel submodelComparisonDisconnected submodelComparisonGLCoefficientGroup submodelComparisonLocalField submodelComparisonMeasurable submodelComparisonT2 submodelComparisonTopology submodelComparisonValuation torusCoefficientEnvelope_of_smooth torusEnvelopeLocalField torusEnvelopeTopology torusEnvelopeValuation tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel whittakerCoefficientIota_matrixConvergesOnRight_of_iota whittakerCoefficient_matrixConvergesOnRight_of_matrix zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement ModelGenericSocleStatement exists_compactOpen_glCoefficientRightStabilizer functionalsCongr mirabolicUnitTest modelGenericSocle modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker

universe uF uV uW

section PadicComparison

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance submodelComparisonMeasurable : MeasurableSpace F := borel F
local instance submodelComparisonBorel : BorelSpace F := ⟨rfl⟩
local instance submodelComparisonT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance submodelComparisonDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance submodelComparisonGLCoefficientGroup {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n π) : AddCommGroup (glCoefficientModel ψ n π ℓ).toSubmodule :=
  (glCoefficientModel ψ n π ℓ).toSubmodule.addCommGroup

/-- A nonzero subrepresentation of the actual coefficient model has the same
gamma expression against the trivial rank-one test whenever both complete
certificates already exist. No irreducibility is required. -/
theorem gamma_eq_submodel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n π ℓ)) (hS : S ≠ ⊥)
    {G GS : RationalFunctions}
    (h : IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) G)
    (hSgamma : IsPadicSymmetricGammaFactor F ψ ν (V := S.toSubmodule) S.toRepresentation
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) GS) : G = GS := by
  let := borel (Langlands.GeneralLinear (0 + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (0 + 1) F)
  let : BorelSpace (GeneralLinear.upperUnipotent (0 + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F)
  rw [isPadicSymmetricGammaFactor_of_le (Nat.zero_le n)] at h hSgamma
  have htest : ∃ ℓ' : glInverseFunctionals ψ 0
      (rankOneCharacter (1 : Fˣ →* ℂˣ)), ℓ'.val ≠ 0 := by
    by_cases hn : n = 0
    · subst n
      exact (isPairGammaFactor_self.mp hSgamma).2.2.1
    · exact ((isPairGammaFactor_of_lt (Nat.pos_of_ne_zero hn)).mp hSgamma).2.2.1
  obtain ⟨ℓ', hℓ'⟩ := htest
  exact (IsPairGammaFactor.eq_of_model_le
    (Langlands.LocalFieldData.residueCardinality_gt_one _)
    (submodelEvaluation_ne_zero π ℓ S hS) hℓ' hℓ hℓ'
    (coefficientModel_submodelEvaluation_le π ℓ S) le_rfl hSgamma h).symm

/-- The actual subquotient map into a submodel supplies the coefficient
inclusion needed by the ambient matrix comparison. The resulting expression
is the original representation's gamma factor, provided a complete gamma
certificate on the original exists. Normalized matrix generators stay on the
ambient representation. -/
theorem gamma_of_submodel_ambient_matrix
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hν : IsSelfDual ψ ν)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n π ℓ)) (hS : S ≠ ⊥)
    (hStype : IsOfWhittakerType (V := S.toSubmodule) n (standardCharacter ψ n)
      S.toRepresentation)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hρ : Langlands.IsSmooth ρ) (A : Subrepresentation ρ)
    (f : A.toRepresentation.IntertwiningMap S.toRepresentation) (hf : Function.Surjective f)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      ρ P PDual c a)
    (hexists : ∃ G, IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) G) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PDual) := by
  let ev := submodelEvaluation π ℓ S
  let q := (modelMap (V := S.toSubmodule) S.toRepresentation ev).comp f
  have hq : Function.Surjective q :=
    (modelMap_surjective (V := S.toSubmodule) S.toRepresentation ev).comp hf
  have hcoeff := Langlands.AllField.GodementJacquet.Padic.subquotientCoefficientInclusion
    F n W (coefficientModel (V := S.toSubmodule) S.toRepresentation ev).toSubmodule
    ρ (modelRepresentation (V := S.toSubmodule) S.toRepresentation ev) hρ A q hq
  have hSgamma := rankOneAmbientMatrixFunctionalEquationComparison
    F ψ ν hν n S.toSubmodule S.toRepresentation hStype
    ev (submodelEvaluation_ne_zero π ℓ S hS) W ρ hcoeff P PDual c a hdata
  obtain ⟨G, hG⟩ := hexists
  obtain rfl := gamma_eq_submodel F ψ ν π ℓ hℓ S hS hG hSgamma
  exact hG

end PadicComparison

end Langlands.AllField.RankinSelberg
