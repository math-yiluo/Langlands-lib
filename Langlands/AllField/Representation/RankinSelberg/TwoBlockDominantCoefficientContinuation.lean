import Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankClearedContinuation
import Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices
/-!
# Actual model coefficient clearing and denominator bounds

Convergence is taken from the actual intrinsic zeta-value witnesses. Full
Whittaker type identifies those coefficients with any fixed nonzero models.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualModelFiniteClearing StrictModelFiniteClearing coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology equalModelFiniteClearing_polynomialDivisibility equalRank_hasBilateralSpectralExpansion strictModelFiniteClearing_polynomialDivisibility unequalRank_hasBilateralSpectralExpansion
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
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance coefficientContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance coefficientContinuationMatrixMeasurable (j n : ℕ) :
    MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F)
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Equal

variable (π : Representation ℂ (GeneralLinear (n + 1) F) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F) W)
  (ell : glFunctionals ψ n π) (ell' : glInverseFunctionals ψ n τ)

/-- Every pair of coefficients in the fixed models, with every actual row
test, has a finite numerator for the specified ordinary clearing polynomial. -/
def EqualModelFiniteClearing (A : Polynomial ℂ) : Prop :=
  ∀ (f : (coefficientModel π ell).toSubmodule)
    (f' : (coefficientModel τ ell').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)),
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ f.val f'.val Φ
    ∃ N : LaurentPolynomial ℂ, ofLaurentPolynomial N = A.toLaurent • a

/-- The actual equal-rank coefficient expansion on a right half-plane. -/
theorem equalRank_hasBilateralSpectralExpansion
    (U : WhittakerFunctions ψ n) (U' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hconv : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      EqualRankConverges ψ abv μ U U' Φ s) :
    HasBilateralSpectralExpansion qF
      (equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ U U' Φ)
      (fun s => equalRankIntegral ψ abv μ U U' Φ s) := by
  obtain ⟨C, hC⟩ := hconv
  exact ⟨C, fun s hs =>
    (equalRankSliceExpansion F (⟨⟩ : LocalFieldData F) n μ ψ U U' Φ s
      (hC s hs)).2.2⟩

/-- Finite clearing on one nonzero model pair controls every intrinsic equal
rank zeta value and yields the required polynomial divisibility direction. -/
theorem equalModelFiniteClearing_polynomialDivisibility
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
    (hell : ell.val ≠ 0) (hell' : ell'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsEqualRankLPolynomial qF ψ abv μ π τ P)
    (hclear : EqualModelFiniteClearing F ψ μ π τ ell ell' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  apply normalizedGenerator_divisibility_of_clearedExpansions
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    (equalRankZetaValues qF ψ abv μ π τ) P A hP hA
  intro R hR
  rw [equalRankZetaValues_eq_model qF ψ abv μ ell ell'
    (hπ.eq_smul hell) (hτ.eq_smul hell')] at hR
  obtain ⟨U, hU, U', hU', Φ, hconv, hcont⟩ := hR
  exact ⟨equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ U U' Φ,
    fun s => equalRankIntegral ψ abv μ U U' Φ s,
    equalRank_hasBilateralSpectralExpansion F ψ μ U U' Φ hconv,
    hcont, hclear ⟨U, hU⟩ ⟨U', hU'⟩ Φ⟩

end Equal

section Strict

variable (j k : ℕ)
  (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
  (π : Representation ℂ (GeneralLinear (n + (j + k + 1) + 1) F) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F) W)
  (ell : glFunctionals ψ (n + (j + k + 1)) π)
  (ell' : glInverseFunctionals ψ n τ)

/-- The actual unequal-rank determinant coefficients in the specified models
have finite numerators after multiplying by the given polynomial. -/
def StrictModelFiniteClearing (A : Polynomial ℂ) : Prop :=
  ∀ (f : (coefficientModel π ell).toSubmodule)
    (f' : (coefficientModel τ ell').toSubmodule),
    let a : BilateralLaurentSeries :=
      unequalRankSliceCoefficient F j k ψ μ ν f.val f'.val
    ∃ N : LaurentPolynomial ℂ, ofLaurentPolynomial N = A.toLaurent • a

/-- Product-space absolute convergence gives the actual unequal-rank spectral
expansion on that same right half-plane. -/
theorem unequalRank_hasBilateralSpectralExpansion [SFinite ν]
    (U : WhittakerFunctions ψ (n + (j + k + 1)))
    (U' : InverseWhittakerFunctions ψ n)
    (hconv : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      UnequalRankConverges ψ abv j k μ ν U U' s) :
    HasBilateralSpectralExpansion qF
      (unequalRankSliceCoefficient F j k ψ μ ν U U')
      (fun s => unequalRankIntegral ψ abv j k μ ν U U' s) := by
  obtain ⟨C, hC⟩ := hconv
  exact ⟨C, fun s hs =>
    (unequalRankSliceExpansion_of_converges F j k ψ μ ν U U' s
      (hC s hs)).2.2⟩

/-- A uniform finite clearing on fixed nonzero models controls the complete
intrinsic unequal-rank L polynomial. No new convergence assumption is needed. -/
theorem strictModelFiniteClearing_polynomialDivisibility [SFinite ν]
    (hπ : IsOfWhittakerType (n + (j + k + 1))
      (standardCharacter ψ (n + (j + k + 1))) π)
    (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
    (hell : ell.val ≠ 0) (hell' : ell'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsUnequalRankLPolynomial qF ψ abv j k μ ν π τ P)
    (hclear : StrictModelFiniteClearing F ψ μ j k ν π τ ell ell' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  apply normalizedGenerator_divisibility_of_clearedExpansions
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    (unequalRankZetaValues qF ψ abv j k μ ν π τ) P A hP hA
  intro R hR
  rw [unequalRankZetaValues_eq_model qF ψ abv j k μ ν ell ell'
    (hπ.eq_smul hell) (hτ.eq_smul hell')] at hR
  obtain ⟨U, hU, U', hU', hconv, hcont⟩ := hR
  exact ⟨unequalRankSliceCoefficient F j k ψ μ ν U U',
    fun s => unequalRankIntegral ψ abv j k μ ν U U' s,
    unequalRank_hasBilateralSpectralExpansion F ψ μ j k ν U U' hconv,
    hcont, hclear ⟨U, hU⟩ ⟨U', hU'⟩⟩

end Strict

end Langlands.AllField.RankinSelberg.DominantRankTransport
