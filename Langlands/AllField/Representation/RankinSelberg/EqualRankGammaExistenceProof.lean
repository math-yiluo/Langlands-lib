import Langlands.Representation.RankinSelberg.EqualRankGammaExistenceProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement
import Langlands.AllField.Representation.RankinSelberg.EqualRankGammaExistenceStatement
import Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearUniquenessProof
import Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType
/-!
# Equal-rank JPSS gamma-factor existence

Combine the proved analytic continuation, Fourier compatibility, normalized
continued forms and trilinear uniqueness on the supplied coefficient models.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFrobenius equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement UnipotentOrbitStatement compactLocalization exists_compactOpen_glCoefficientRightStabilizer functionalsCongr mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- A single rational gamma comparison for all equal-rank test triples,
with the supplied topology, quotient measure and self-dual Fourier measure. -/
theorem equalRankGammaExistence
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    EqualRankGammaExistenceStatement.{uF,uV,uW} F T n := by
  have hAnalytic := equalRankAnalytic.{uF,uV,uW} F T n
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := equalRankGamma_valuative_nonarchimedean (K := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  unfold EqualRankGammaExistenceStatement
  intro ψ hRight μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hA := hAnalytic ψ μ hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hAd := hAnalytic (ψ.scale (-1)) μ hμ V W
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
  have hF := (rowFourierCompatibility ψ ν (n + 1) hν).1
  obtain ⟨P, hP⟩ := hA.2.2.2
  obtain ⟨Pd, hPd⟩ := hAd.2.2.2
  have hPdual : IsNormalizedGenerator
      (dualEqualRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ') Pd := by
    simpa only [dualEqualRankRationalValues_eq] using hPd
  obtain ⟨B, Bd, hInv, hEval⟩ :=
    equalRankContinuedForms F T n ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      hA hAd hF P Pd hP hPdual
  obtain ⟨E, hE⟩ := equalRankTrilinearUniqueness F T n ψ V W π σ hπ hσ ℓ ℓ'
  exact EqualRankGammaReduction.gammaEquation_of_continuedForms T.residueCardinality_gt_one hσ hA hAd hF
    P Pd hP hPdual.polynomial_ne_zero B Bd
    (fun f f' Φ Φhat R Rd hPair hR hRd s =>
      hEval f f' Φ Φhat hPair R Rd hR hRd s)
    E (fun s hs => hE s hs (B s) (Bd s) (hInv s).1 (hInv s).2)

end Langlands.AllField.RankinSelberg
