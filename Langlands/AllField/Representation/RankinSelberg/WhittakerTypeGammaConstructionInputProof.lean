import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFunctionalEquationProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputStatement
/-! Canonical symmetric gamma construction inputs from the published JPSS
analytic and functional-equation theorems. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeGammaConstructionInputStatement ZeroRowLastRowCutoffStatement centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaConstructionInput_of_whittakerType padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerTypeGammaConstructionInput zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement UnipotentOrbitStatement compactLocalization exists_compactOpen_glCoefficientRightStabilizer functionalsCongr mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Whittaker type supplies all canonical construction inputs when the larger
rank is first and the second representation has inverse-standard type. -/
theorem padicPairGammaConstructionInput_of_whittakerType
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hnr : n ≤ r) :
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
    PadicPairGammaConstructionInput F ψ ν.val π σ := by
  let := (⟨⟩ : LocalFieldData F).fieldT2
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hπ hσ
  have hμ := unipotentQuotientHaar_isCompatible F n
  have hA :
      ∀ (χ : UnitaryAdditiveCharacter F)
        (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
        (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter χ r) ρ →
        IsOfWhittakerType n (inverseStandardCharacter χ n) τ →
        PairAnalyticInput (⟨⟩ : LocalFieldData F).residueCardinality χ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (unipotentQuotientHaar F n) ν.val ρ τ := by
    intro χ ρ τ hρ hτ
    by_cases hr : r = n
    · subst r
      simp only [PairAnalyticInput]
      intro ℓ ℓ' hℓ hℓ'
      exact equalRankAnalytic.{uF, uV, uW} F (⟨⟩ : LocalFieldData F) n
        χ (unipotentQuotientHaar F n) hμ V W ρ τ hρ hτ ℓ ℓ' hℓ hℓ'
    · simp only [PairAnalyticInput, dite_eq_right hr]
      intro ℓ ℓ' hℓ hℓ' j k hrank
      subst r
      exact unequalRankAnalytic.{uF, uV, uW} F (⟨⟩ : LocalFieldData F) n j k
        χ (unipotentQuotientHaar F n) hμ ν.val V W ρ τ hρ hτ ℓ ℓ' hℓ hℓ'
  have hε : PairEpsilonFactorExists (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) ν.val π σ := by
    obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
    obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
    by_cases hr : r = n
    · subst r
      have hFE := equalRankFunctionalEquation.{uF, uV, uW}
        F (⟨⟩ : LocalFieldData F) n ψ
        (unipotentQuotientHaar F n) hμ ν.val ν.property
        V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      obtain ⟨c, m, hcm⟩ := exists_equalRankEpsilonEquation_iff.mpr hFE
      exact ⟨(c, m), isPairEpsilonFactor_self.mpr
        (equalRankEpsilonFactor_of_equation hπ hσ hℓ hℓ' hcm)⟩
    · have hlt : n < r := by omega
      have hFE := unequalRankFunctionalEquation.{uF, uV, uW}
        F (⟨⟩ : LocalFieldData F) n r hlt ψ
        (unipotentQuotientHaar F n) hμ ν.val ν.property
        V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      obtain ⟨c, m, hcm⟩ := exists_unequalRankEpsilonEquation_iff.mpr hFE
      exact ⟨(c, m), (isPairEpsilonFactor_of_lt hlt).mpr
        (unequalRankEpsilonFactor_of_equation hlt hπ hσ hℓ hℓ' hcm)⟩
  exact ⟨hnr, ν.property, hε, hπ, hσ, hA ψ π σ hπ hσ,
    hA (ψ.scale (-1)) (inverseTransposePullback π) (inverseTransposePullback σ)
      (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)⟩

/-- Standard Whittaker type of both original representations supplies the
canonical symmetric gamma construction input for every positive rank pair. -/
theorem whittakerTypeGammaConstructionInput :
    WhittakerTypeGammaConstructionInputStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r n V _ _ W _ _ π σ
  intro hπ hσ
  by_cases hnr : n ≤ r
  · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_left hnr] using
      padicPairGammaConstructionInput_of_whittakerType.{uF, uV, uW}
        F ψ ν r n V W π σ hnr
        hπ ((isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ)
  · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_right hnr] using
      padicPairGammaConstructionInput_of_whittakerType.{uF, uW, uV}
        F ψ ν n r W V σ π (by omega)
        hσ ((isOfWhittakerType_standard_iff_inverse ψ π).mp hπ)

end Langlands.AllField.RankinSelberg
