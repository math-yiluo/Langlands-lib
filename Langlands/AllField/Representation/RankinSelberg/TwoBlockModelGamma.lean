import Langlands.Representation.RankinSelberg.TwoBlockModelGamma
import Langlands.AllField.Representation.GodementJacquet.GenericMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneTestReduction
import Langlands.AllField.Representation.RankinSelberg.SubmodelGammaComparison
import Langlands.AllField.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
/-!
# Two-block gamma comparison through the actual generic model socles

Generic matrix functional-equation existence remains an explicit premise.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput PairedMatrixBlockComparison PrincipalDualAssertions QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneAmbientMatrixFunctionalEquationComparisonStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RawModelIotaMatrixConvergence RootTorusProductStatement SliceIntegrable SliceIntegrableAt TorusCoefficientEnvelope TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockModelGenericSocleOccurrenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement WhittakerTypeGammaConstructionInputStatement ZeroRowLastRowCutoffStatement ambientComparisonGLBorel ambientComparisonGLMeasurable ambientComparisonLocalField ambientComparisonQuotientBorel ambientComparisonQuotientMeasurable ambientComparisonScalarBorel ambientComparisonScalarMeasurable ambientComparisonT2 ambientComparisonTopology ambientComparisonTotallyDisconnected ambientComparisonUnipotentBorel ambientComparisonUnipotentMeasurable ambientComparisonValuation ambientZeroGLBorel ambientZeroGLMeasurable ambientZeroLocalField ambientZeroQuotientBorel ambientZeroQuotientMeasurable ambientZeroScalarMeasurable ambientZeroTopology ambientZeroUnipotentBorel ambientZeroUnipotentMeasurable ambientZeroValuation biSmooth_matrixDiagonal_convergesOnRight boundedDiagonalNormIntegrand boundedDiagonalNormIntegrand_convergesOnRight boundedDiagonalNormIntegrand_le_matrixDiagonal boxDiagonalLocalField boxDiagonalTopology boxDiagonalUnitsBorel boxDiagonalUnitsMeasurable boxDiagonalValuativeRel boxLatticeTest_fourier_rightLeadingSign boxLatticeTest_rightLeadingSign centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus coefficientModelEvaluation_coefficient compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_determinantOrder continuous_ord_units continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantNorm_rankOneSignedWeyl determinantNorm_rankOneWeylLeadingSign determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement determinantWeight_principalSignedBlockPoint diagonalBorelDensity diagonalConj_map diagonalSliceWeight diagonalSliceWeight_nonneg diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice dualFunction_blockMatrixAt_rankCast enorm_weightedCoefficient_sub_natCast equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support exists_uniform_matrixUnipotentNormSlice_bound finiteFunctionMellin finiteFunctionShellSeries gamma_eq_submodel gamma_of_submodel_ambient_matrix glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice integrable_biSmooth_matrixDiagonalIntegrand integrable_diagonalUnits_of_principalFixed integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_principalFixedBlockIntegrand_signedDual_iff integrable_principalModelBlockIntegrand_of_fixed integrable_principalModelFourierIntegrand_signedDual_iff integrable_prod_generalLinear_one_natWeight_iff integrable_rankOneDualBlockIntegrand_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_principalFixedBlockIntegrand_signedDual integral_principalModelBlockIntegrand_of_fixed integral_principalModelFourierIntegrand_signedDual integral_prod_generalLinear_one_natWeight integral_rankOneDualBlockIntegrand inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClopen_matrixNormBox isClosed_determinantSlice isCompact_matrixNormBox isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_one_swap isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lintegral_iwasawa_diagonalBorelDensity lintegral_norm_matrixIntegrand_iwasawa matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation matrixConvergesOnRight_inverseTransposePullback matrixConvergesOnRight_of_torusEnvelope matrixDiagonalIntegrand matrixIntegrand_exists_principalFixed matrixNormBox matrixNormBoxTest matrixNormBoxTest_diagonal_of_le matrixUnipotentNormSlice measurableSet_determinantSlice measurable_biSmooth_matrixIntegrand measurable_boundedDiagonalNormIntegrand measure_diagonalUnits_preimage_principalLevel_le_one mem_determinantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelDataLocalField modelDataTopology modelDataValuativeRel modelGammaCoefficientGroup modelGammaTopology normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaConstructionInput_of_whittakerType padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairedComparisonGLBorel pairedComparisonGLMeasurable pairedComparisonLocalField pairedComparisonQuotientBorel pairedComparisonQuotientMeasurable pairedComparisonScalarMeasurable pairedComparisonTopology pairedComparisonUnipotentBorel pairedComparisonUnipotentMeasurable pairedComparisonValuativeRel pairwise_disjoint_determinantSlice parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalDualGLBorel principalDualGLMeasurable principalDualLocalField principalDualQuotientMeasurable principalDualScalarBorel principalDualScalarMeasurable principalDualT2 principalDualTopology principalDualTotallyDisconnected principalDualUnipotentBorel principalDualUnipotentMeasurable principalDualValuation principalDual_value principalFixedBlockIntegrand principalFixedBlockIntegrand_density principalFixedDualBorel principalFixedDualGLBorel principalFixedDualGLMeasurable principalFixedDualGLSecondCountable principalFixedDualLocalField principalFixedDualMeasurable principalFixedDualSecondCountable principalFixedDualT2 principalFixedDualTopology principalFixedDualTotallyDisconnected principalFixedDualValuativeRel principalFixedModelDual_pairing principalModelBlockIntegrand principalModelBlockIntegrand_ae_of_fixed principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalModelFourierIntegrand_signedDual_eq principalSignedBlockPoint quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientIwasawaIntegration quotientRootIntegration rankOneAmbientMatrixFunctionalEquationComparison rankOneAmbientMatrixFunctionalEquationComparison_zero rankOneAmbientModelMatrixCoefficient rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneDualBlockIntegrand rankOneDualBlockIntegrand_eq_quotient rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneGammaTwist rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneSignedDualHomeomorph rankOneSignedDualHomeomorph_apply rankOneSignedDualHomeomorph_preserving rankOneWhittakerType rankOne_blockZero_exists_ne_zero rawMatrixGLBorel rawMatrixGLMeasurable rawMatrixLocalField rawMatrixNBorel rawMatrixNMeasurable rawMatrixSecondCountable rawMatrixT2 rawMatrixTopology rawMatrixUnitsBorel rawMatrixUnitsMeasurable rawMatrixUnitsSecondCountable rawMatrixValuativeRel rawModelIotaMatrixConvergence_of_modelIota rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel setIntegral_equalRankIntegrand_determinantSlice signedBlockGLParameterIntegrand signedDualBlockGLBorel signedDualBlockGLMeasurable signedDualBlockGLSigmaCompact signedDualBlockLocalField signedDualBlockQuotientBorel signedDualBlockQuotientMeasurable signedDualBlockScalarBorel signedDualBlockScalarMeasurable signedDualBlockSecondCountable signedDualBlockT2 signedDualBlockTopology signedDualBlockUnipotentBorel signedDualBlockUnipotentMeasurable signedDualBlockValuation signedDualTransportGLBorel signedDualTransportGLMeasurable signedDualTransportLocalField signedDualTransportScalarMeasurable signedDualTransportTopology signedDualTransportValuation signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable smoothDiagonalGLBorel smoothDiagonalGLLocallyCompact smoothDiagonalGLMeasurable smoothDiagonalGLSecondCountable smoothDiagonalLocalField smoothDiagonalSecondCountable smoothDiagonalT2 smoothDiagonalTopology smoothDiagonalUnitsBorel smoothDiagonalUnitsMeasurable smoothDiagonalUnitsSecondCountable smoothDiagonalValuativeRel smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel submodelComparisonBorel submodelComparisonDisconnected submodelComparisonGLCoefficientGroup submodelComparisonLocalField submodelComparisonMeasurable submodelComparisonT2 submodelComparisonTopology submodelComparisonValuation torusCoefficientEnvelope_of_smooth torusEnvelopeLocalField torusEnvelopeTopology torusEnvelopeValuation tsupport_boxLatticeTest_subset twoBlockGammaRankOne_of_generic_matrix twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test twoBlockModelGenericSocleOccurrence unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel whittakerCoefficientIota_matrixConvergesOnRight_of_iota whittakerCoefficient_matrixConvergesOnRight_of_matrix whittakerTypeGammaConstructionInput zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset measurePreserving_rectangular_mul_mul mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement ModelGenericSocleStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelGenericSocle modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uW

/-- The complete symmetric gamma certificate is unchanged by putting the
trivial scalar test first, including the equal-rank case. -/
theorem isPadicSymmetricGammaFactor_rankOne_one_swap
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν σ (rankOneCharacter 1) G ↔
      IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter 1) σ G := by
  cases n with
  | zero =>
    simp only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true]
    exact isPadicPairGammaFactor_swap_equalRank F ψ ν σ (rankOneCharacter 1)
      hσ (rankOneCharacter_isOfWhittakerType F ψ 1) G
  | succ n =>
    simp only [IsPadicSymmetricGammaFactor, Nat.zero_le,
      show ¬ n + 1 ≤ 0 by omega, ite_true, ite_false]

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelGammaCoefficientGroup {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Restrict the smooth Schur character to the actual scalar matrices. -/
private theorem modelGamma_scalarQuasicharacter {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    ∃ ω : Quasicharacter F,
      Classification.HasGLCentralCharacter F (n + 1) σ ω.toMonoidHom := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter σ ha hi
  let ω : Quasicharacter F :=
    ⟨χ.comp GeneralLinear.scalarToCenter,
      hlc.continuous.comp (GeneralLinear.scalarContinuous.continuous.subtype_mk _)⟩
  exact ⟨ω, fun x v => hact (GeneralLinear.scalarToCenter x) v⟩

/-- Full Whittaker type supplies a complete gamma certificate independently
of the matrix comparison. -/
private theorem modelGamma_exists
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ G, IsPadicSymmetricGammaFactor F ψ ν.val σ (rankOneCharacter 1) G := by
  let G := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val σ (rankOneCharacter 1)
    (whittakerTypeGammaConstructionInput F ψ ν n 0 V ℂ σ (rankOneCharacter 1)
      hσ (rankOneCharacter_isOfWhittakerType F ψ 1))
  exact ⟨G.val, G.property⟩

/-- Data on a nonzero full-type submodel determine the gamma certificate of
the possibly reducible original. -/
private theorem modelGamma_from_submodel_data
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (S : Subrepresentation (glModelRepresentation ψ n σ ℓ)) (hS : S ≠ ⊥)
    (hStype : IsOfWhittakerType (V := S.toSubmodule)
      n (standardCharacter ψ n) S.toRepresentation)
    (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hdata : Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν.val
      (V := S.toSubmodule) S.toRepresentation P PD c a) :
    IsPadicSymmetricGammaFactor F ψ ν.val σ (rankOneCharacter 1)
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PD) := by
  let q : (⊤ : Subrepresentation S.toRepresentation).toRepresentation.IntertwiningMap
      S.toRepresentation :=
    { toLinearMap := (⊤ : Subrepresentation S.toRepresentation).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact gamma_of_submodel_ambient_matrix F ψ ν.val ν.property σ ℓ hℓ S hS hStype
    S.toRepresentation hStype.1.1 ⊤ q (fun v => ⟨⟨v, trivial⟩, rfl⟩)
    P PD c a hdata (modelGamma_exists F ψ ν σ hσ)

end Padic

set_option maxHeartbeats 800000 in
/-- The unchanged rank-one gamma target follows from full matrix data
existence on irreducible generic models. The analytic premise is explicit. -/
theorem twoBlockGammaRankOne_of_generic_matrix
    (hG : Langlands.AllField.GodementJacquet.GenericMatrixFunctionalEquationStatement.{uF,uF}) :
    TwoBlockGammaRankOneStatement.{uF,uV,uW} := by
  apply twoBlockGammaRankOne_of_trivial_test
  intro F _ _ _ _ ψ ν t m h W hadd hmod σ hσ
  classical
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  let : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : ∀ r : ℕ, MeasurableSpace (Langlands.GeneralLinear r F) :=
    fun _ => borel _
  let : ∀ r : ℕ, BorelSpace (Langlands.GeneralLinear r F) :=
    fun _ => ⟨rfl⟩
  choose ℓ hℓ using fun i => (hσ i).exists_ne_zero
  let : ∀ i, AddCommGroup (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  choose Si hSi using fun i =>
    modelGenericSocle F ψ (m i) (W i) (σ i) (hσ i) (ℓ i) (hℓ i)
  let R (i : Fin 2) : Type uF := (Si i).toSubmodule
  let : ∀ i, AddCommGroup (R i) := fun i => (Si i).toSubmodule.addCommGroup
  let : ∀ i, Module ℂ (R i) := fun i => inferInstance
  let τ (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (m i + 1) F) (R i) := (Si i).toRepresentation
  have hτ (i : Fin 2) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) :=
    (hSi i).2.2.2
  choose P PD c a hdata using fun i =>
    hG F ψ ν.val ν.property (m i) (R i) (τ i) (hτ i) (hSi i).2.1
  choose ω hω using fun i =>
    modelGamma_scalarQuasicharacter F (τ i) (hτ i).1 (hSi i).2.1
  let I := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType F ψ t 2 m h σ hσ
  obtain ⟨ℓI, hℓI⟩ := hI.exists_ne_zero
  let : AddCommGroup (glCoefficientModel ψ t I ℓI).toSubmodule :=
    (glCoefficientModel ψ t I ℓI).toSubmodule.addCommGroup
  obtain ⟨S, hS⟩ := modelGenericSocle F ψ t _ I hI ℓI hℓI
  let J := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) τ
  have hJ : IsSmooth J :=
    (⟨⟩ : LocalFieldData F).isSmooth_normalizedProductInduced
      (succBlockShape m h) τ
  have hJdata : Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData
      F ψ ν.val J (∏ i, P i) (∏ i, PD i) (∏ i, c i) (∑ i, a i) :=
    Langlands.AllField.GodementJacquet.twoBlockMatrixFunctionalEquationInduction F t m h R τ
      (fun i => (hτ i).1.1) (fun i => (hτ i).1) ψ ν.val ν.property ω hω P PD c a hdata
  obtain ⟨A, q, hq⟩ := twoBlockModelGenericSocleOccurrence F ψ t m h W σ hσ
    ℓ hℓ ℓI hℓI Si S hSi hS
  have hIgamma := gamma_of_submodel_ambient_matrix F ψ ν.val ν.property I ℓI hℓI
    S hS.1 hS.2.2.2 J hJ A q hq (∏ i, P i) (∏ i, PD i)
    (∏ i, c i) (∑ i, a i) hJdata (modelGamma_exists F ψ ν I hI)
  let G (i : Fin 2) :=
    rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) (c i) (a i) (P i) (PD i)
  refine ⟨G, fun i => ?_, ?_⟩
  · apply (isPadicSymmetricGammaFactor_rankOne_one_swap F ψ ν.val (σ i) (hσ i) (G i)).1
    exact modelGamma_from_submodel_data F ψ ν (σ i) (hσ i) (ℓ i) (hℓ i)
      (Si i) (hSi i).1 (hτ i) (P i) (PD i) (c i) (a i) (hdata i)
  · apply (isPadicSymmetricGammaFactor_rankOne_one_swap F ψ ν.val I hI (∏ i, G i)).1
    simpa only [rationalGammaExpression_prod_two] using hIgamma

end Langlands.AllField.RankinSelberg
