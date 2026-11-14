import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualModelFiniteClearing StrictModelFiniteClearing coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology equalModelFiniteClearing_polynomialDivisibility equalRank_hasBilateralSpectralExpansion strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictCoefficient_continuationData strictCoefficient_polynomialDivisibility strictContinuationGLBorel strictContinuationGLMeasurable strictContinuationLocalField strictContinuationMeasurable strictContinuationQuotientMeasurable strictContinuationSigmaCompact strictContinuationTopology strictContinuationUnipotentBorel strictContinuationUnipotentMeasurable strictContinuationValuation strictIntegral_eq strictModelFiniteClearing_polynomialDivisibility strictRankAnalyticAt strictRectangleMeasure strictRectangleMeasure_sigmaFinite strictSliceCoefficient strictSliceCoefficient_lowerSupport unequalRankSliceCoefficient_lowerSupport unequalRank_hasBilateralSpectralExpansion
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement adjacentRankUnipotentFourier padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictContinuationSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance strictContinuationMeasurable : MeasurableSpace F := borel _
local instance strictContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance strictContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance strictContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance strictContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance strictContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _

private theorem property_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁)
    (P : (m : MeasurableSpace X) → @Measure X m → Prop)
    (hP : P m₁ μ) : P m₂ (hm ▸ μ) := by
  cases hm
  exact hP

private theorem integral_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁) (φ : X → ℂ) :
    (letI := m₂; ∫ x, φ x ∂(hm ▸ μ)) =
      (letI := m₁; ∫ x, φ x ∂μ) := by
  cases hm
  rfl

/-- The supplied rectangle product remains sigma-finite under the canonical
Borel measurable-space identification. -/
instance strictRectangleMeasure_sigmaFinite (ν : AdditiveHaarMeasure F)
    (j n : ℕ) : SigmaFinite (strictRectangleMeasure F ν j n) := by
  exact property_measurableSpace_transport _ (rectangularMeasure ν j n)
    (fun m μ => @SigmaFinite _ m μ) inferInstance

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {n r j k : ℕ}
  (hr : r = n + (j + k + 1))
  (ψ : UnitaryAdditiveCharacter F)
  (μ : Measure (LeftUnipotentQuotient n F))
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F) W)
  (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n σ)

/-- Published unequal-rank analysis for the exact supplied Haar rectangle,
transporting only its measurable-space presentation. -/
theorem strictRankAnalyticAt
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0) :
    letI := borel (Matrix (Fin j) (Fin (n + 1)) F)
    UnequalRankAnalyticAt j k hr qF ψ abv μ
      (strictRectangleMeasure F ν j (n + 1)) π σ lambda ell := by
  subst r
  have hA := unequalRankAnalytic F (⟨⟩ : LocalFieldData F) n j k ψ μ hμ ν
    V W π σ hπ hσ lambda ell hlambda hell
  exact property_measurableSpace_transport _ (rectangularMeasure ν j (n + 1))
    (fun m νR => letI := m
      UnequalRankAnalyticAt j k rfl qF ψ abv μ νR π σ lambda ell) hA

/-- The fixed-rank Borel rectangle integral is exactly the original supplied
product-Haar integral. -/
theorem strictIntegral_eq
    (U : WhittakerFunctions ψ r) (U' : InverseWhittakerFunctions ψ n) :
    (letI := borel (Matrix (Fin j) (Fin (n + 1)) F);
      unequalRankIntegral ψ abv j k μ (strictRectangleMeasure F ν j (n + 1))
        (hr ▸ U) U') =
      unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) U U' := by
  subst r
  funext s
  apply integral_congr_ae
  filter_upwards [] with z
  exact integral_measurableSpace_transport _ _ _

/-- The actual strict coefficients expand the original supplied-Haar integral
on a right half-plane; the same integral has a rational continuation. -/
theorem strictCoefficient_continuationData
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (f : (coefficientModel π lambda).toSubmodule)
    (f' : (coefficientModel σ ell).toSubmodule) :
    HasBilateralSpectralExpansion qF (strictSliceCoefficient F hr ψ μ ν f.val f'.val)
      (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
        f.val f'.val) ∧
    ∃ R : RationalFunctions, HasRationalContinuation qF
      (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
        f.val f'.val) R := by
  have hA := strictRankAnalyticAt F hr ψ μ ν π σ lambda ell hμ hπ hσ hlambda hell
  subst r
  have hI := strictIntegral_eq F rfl ψ μ ν f.val f'.val
  obtain ⟨R, hR⟩ := hA.2.1 f f'
  refine ⟨?_, R, ?_⟩
  · rw [← hI]
    exact unequalRank_hasBilateralSpectralExpansion F ψ μ j k
      (strictRectangleMeasure F ν j (n + 1)) f.val f'.val (hA.1 f f')
  · change HasRationalContinuation qF
      (letI := borel (Matrix (Fin j) (Fin (n + 1)) F);
        unequalRankIntegral ψ abv j k μ (strictRectangleMeasure F ν j (n + 1))
          f.val f'.val) R at hR
    rwa [hI] at hR

/-- Uniform clearing of the actual fixed-rank coefficients controls the
intrinsic normalized generator for the original supplied product measure. -/
theorem strictCoefficient_polynomialDivisibility
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsNormalizedGenerator
      (unequalRankZetaValuesAt j k hr qF ψ abv μ
        (rectangularMeasure ν j (n + 1)) π σ) P)
    (hclear : ∀ (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel σ ell).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N =
          A.toLaurent • strictSliceCoefficient F hr ψ μ ν f.val f'.val) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  subst r
  have hPBorel :
      letI := borel (Matrix (Fin j) (Fin (n + 1)) F)
      IsUnequalRankLPolynomial qF ψ abv j k μ
        (strictRectangleMeasure F ν j (n + 1)) π σ P :=
    property_measurableSpace_transport _ (rectangularMeasure ν j (n + 1))
      (fun m νR => letI := m
        IsUnequalRankLPolynomial qF ψ abv j k μ νR π σ P) hP
  exact strictModelFiniteClearing_polynomialDivisibility F ψ μ j k
    (strictRectangleMeasure F ν j (n + 1)) π σ lambda ell
    hπ hσ hlambda hell P A hA hPBorel hclear

end Langlands.AllField.RankinSelberg.DominantRankTransport
