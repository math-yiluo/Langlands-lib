import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictEntireSlices
import Langlands.AllField.Representation.RankinSelberg.CorankSliceFiniteEvaluation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDiagonalSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictContinuation
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualModelFiniteClearing StrictModelFiniteClearing StrictRankEntireSliceData coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology equalModelFiniteClearing_polynomialDivisibility equalRank_hasBilateralSpectralExpansion strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictCoefficient_continuationData strictCoefficient_polynomialDivisibility strictContinuationGLBorel strictContinuationGLMeasurable strictContinuationLocalField strictContinuationMeasurable strictContinuationQuotientMeasurable strictContinuationSigmaCompact strictContinuationTopology strictContinuationUnipotentBorel strictContinuationUnipotentMeasurable strictContinuationValuation strictEntireBorel strictEntireLocalField strictEntireMeasurable strictEntireQuotientBorel strictEntireQuotientMeasurable strictEntireSecondCountable strictEntireSigmaCompact strictEntireT2 strictEntireTopology strictEntireValuation strictIntegral_eq strictModelFiniteClearing_polynomialDivisibility strictRankAnalyticAt strictRectangleMeasure strictRectangleMeasure_sigmaFinite strictSliceCoefficient strictSliceCoefficient_eq_restrictedIntegral strictSliceCoefficient_lowerSupport strictSlices_entire strictZeroRowSlice_entire unequalRankSliceCoefficient_lowerSupport unequalRank_hasBilateralSpectralExpansion
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement adjacentRankUnipotentFourier padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis.BilateralLaurentSeries
open Langlands.RankinSelberg.ParameterSpecialization

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictEntireT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance strictEntireSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance strictEntireSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance strictEntireMeasurable : MeasurableSpace F := borel _
local instance strictEntireBorel : BorelSpace F := ⟨rfl⟩
local instance strictEntireQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance strictEntireQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

open Langlands.RankinSelberg.CommonLevel hiding corank_common_compact_support corank_diagonal_upper corank_slice_of_common_support diagonalAnnulusImage diagonalAnnulusImage_isCompact exists_uniform_lattice ord_det_of_mem_integralSubgroup root_bound
open Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.AdjacentBlockReduction

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "abv" => normalizedAbsoluteValue T

/-- The literal fixed-rank coefficient is the actual integral at zero with its
quotient measure restricted to the determinant slice. -/
theorem strictSliceCoefficient_eq_restrictedIntegral {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (U : WhittakerFunctions ψ r) (U' : InverseWhittakerFunctions ψ n) (a : ℤ) :
    strictSliceCoefficient F hr ψ μ ν U U' a =
      unequalRankIntegralAt j k hr ψ abv (μ.restrict (determinantSlice T n a))
        (rectangularMeasure ν j (n + 1)) U U' 0 := by
  subst r
  exact congrFun (strictIntegral_eq F rfl ψ
    (μ.restrict (determinantSlice T n a)) ν U U') 0

private theorem strictEntire_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (rankInclusionContinuous 1).continuous.comp ih

section ZeroRows

variable {n k : ℕ} (ψ : UnitaryAdditiveCharacter F)
  (μ : Measure (LeftUnipotentQuotient n F))
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (n + (0 + k + 1) + 1) F) V)
  (hπ : IsSmooth π) (lambda : glFunctionals ψ (n + (0 + k + 1)) π)
  (W : (coefficientModel π lambda).toSubmodule)
  (U : ℂ → InverseWhittakerFunctions ψ n)
  (K : Subgroup (GeneralLinear (n + 1) F))
  (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F)))
  (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F) (k : K),
    (U u).val (g * k) = (U u).val g)
  (hU : ∀ (g : GeneralLinear (n + 1) F) (u : ℂ),
    AnalyticAt ℂ (fun z => (U z).val g) u)

include hπ K hKo hK hU

set_option maxHeartbeats 1600000 in
/-- At zero rectangular rows, compact diagonal slice support and a common right
level express every actual coefficient as a finite sum of entire point values. -/
theorem strictZeroRowSlice_entire [IsFiniteMeasureOnCompacts μ] :
    EntireCoefficientFamily (fun u => strictSliceCoefficient F rfl ψ μ ν W.val (U u)) := by
  classical
  obtain ⟨K1, hK1⟩ := model_isSmooth π hπ lambda W
  let G := GeneralLinear (n + 1) F
  let N := upperUnipotent (n + 1) F
  let J : Subgroup G := K1.toSubgroup.comap (appendIdentity n (0 + k + 1)) ⊓ K ⊓
    Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  have hIo : IsOpen
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n : Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact (Conductor.levelOpenSubgroup F n 0).isOpen
  have hIc : IsCompact
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n : Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F n 0
  have hJo : IsOpen (J : Set G) :=
    ((K1.isOpen.preimage (strictEntire_continuous_appendIdentity F n (0 + k + 1))).inter hKo).inter hIo
  have hJc : IsCompact (J : Set G) :=
    hIc.of_isClosed_subset (J.isClosed_of_isOpen hJo) fun z hz => hz.2
  let ρ := strictRectangleMeasure F ν 0 (n + 1)
  let f : ℂ → LeftUnipotentQuotient n F → ℂ := fun z =>
    unequalRankAverage F 0 k ψ ρ W.val (U z) 0
  have hf (z : ℂ) (g : G) : f z (Quotient.mk _ g) =
      (ρ.real Set.univ : ℂ) * W.val.val (appendIdentity n (0 + k + 1) g) *
        (U z).val g * determinantWeight abv g (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
    simp only [f, unequalRankAverage, unequalRankIntegrand_mk,
      unequalRankMatrix_zero_rows, integral_const, Complex.real_smul]
    ring
  have hfJ : ∀ z q, ∀ a ∈ J, f z (rightTranslate N a q) = f z q := by
    intro z q a ha
    induction q using Quotient.inductionOn with
    | h g =>
      change f z (Quotient.mk _ (g * a)) = f z (Quotient.mk _ g)
      rw [hf, hf, map_mul]
      have hW : W.val.val (appendIdentity n (0 + k + 1) g * appendIdentity n (0 + k + 1) a) =
          W.val.val (appendIdentity n (0 + k + 1) g) :=
        congrArg (fun f : (coefficientModel π lambda).toSubmodule =>
          f.val.val (appendIdentity n (0 + k + 1) g)) (hK1 ⟨_, ha.1.1⟩)
      rw [hW, hK z g ⟨a, ha.1.2⟩]
      have hd : determinantWeight abv (g * a) (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) =
          determinantWeight abv g (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
        unfold determinantWeight
        rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbsoluteValue_apply T
          (Matrix.det a.val), normalizedAbs_det_of_mem_integralSubgroup T ha.2, mul_one]
      rw [hd]
  intro a z0
  let S := determinantSlice T n a
  let normProfile : LeftUnipotentQuotient n F → ℝ :=
    S.indicator (whittakerNorm ψ (diagonalWhittaker ψ (0 + k + 1) W.val))
  let C := tsupport normProfile
  have hC : IsCompact C :=
    (diagonalWhittaker_slice_hasCompactSupport F n (0 + k) ψ π hπ lambda W a).isCompact
  have hCS : IsCompact (C ∩ S) := hC.inter_right (isClosed_determinantSlice T n a)
  have hsuppC : ∀ z, ∀ q ∈ S, f z q ≠ 0 → q ∈ C ∩ S := by
    intro z q hq hne
    refine ⟨subset_tsupport normProfile ?_, hq⟩
    change normProfile q ≠ 0
    dsimp only [normProfile]
    rw [Set.indicator_of_mem hq]
    induction q using Quotient.inductionOn with
    | h g =>
      rw [whittakerNorm_mk]
      apply norm_ne_zero_iff.mpr
      intro hz
      apply hne
      rw [hf]
      change (ρ.real Set.univ : ℂ) * (diagonalWhittaker ψ (0 + k + 1) W.val).val g *
        (U z).val g * _ = 0
      rw [hz, mul_zero, zero_mul, zero_mul]
  have hSJ : ∀ q ∈ S, ∀ a ∈ J, rightTranslate N a q ∈ S := by
    intro q hq a ha
    rw [rightTranslate_mem_determinantSlice, ord_det_of_mem_integralSubgroup T ha.2, sub_zero]
    exact hq
  obtain ⟨points, hpC, hdisj, hcover⟩ := exists_finset_rightTranslateOrbit_cover N hJo hCS
  have horbit : ∀ z, IntegrableOn (f z) S μ ∧
      ∫ q in S, f z q ∂μ =
        ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    fun z => integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit N μ hJo hJc
      (measurableSet_determinantSlice T n a) hSJ points (fun q hq => (hpC q hq).2)
      hdisj (f z) (hfJ z) fun q hq hne => hcover (hsuppC z q hq hne)
  have heq : (fun z => strictSliceCoefficient F rfl ψ μ ν W.val (U z) a) =
      fun z => ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    funext fun z => (horbit z).2
  rw [heq]
  refine Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul ?_
  induction q using Quotient.inductionOn with
  | h g =>
    change AnalyticAt ℂ (fun z => f z (Quotient.mk _ g)) z0
    simp_rw [hf]
    exact ((analyticAt_const.mul (hU g z0)).mul analyticAt_const)

end ZeroRows

/-- The literal fixed-rank determinant-slice coefficient family is entire. -/
def StrictRankEntireSliceData {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ r) (U : ℂ → InverseWhittakerFunctions ψ n) : Prop :=
  EntireCoefficientFamily (fun u => strictSliceCoefficient F hr ψ μ ν W (U u))

set_option maxHeartbeats 1600000 in
/-- Entire point values at one common right level give entire actual strict
slice coefficients at every rectangular row. Full type supplies the uniform
rectangular support used to integrate each row within the original model. -/
theorem strictSlices_entire {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]
    (ν : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π) (hlambda : lambda.val ≠ 0)
    (W : (coefficientModel π lambda).toSubmodule)
    (U : ℂ → InverseWhittakerFunctions ψ n)
    (K : Subgroup (GeneralLinear (n + 1) F))
    (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F)))
    (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F) (a : K),
      (U u).val (g * a) = (U u).val g)
    (hU : ∀ (g : GeneralLinear (n + 1) F) (u : ℂ),
      AnalyticAt ℂ (fun z => (U z).val g) u) :
    StrictRankEntireSliceData F hr ψ μ ν W.val U := by
  classical
  induction j generalizing k W with
  | zero =>
    subst r
    exact strictZeroRowSlice_entire F ψ μ ν π hπ.1.1 lambda W U K hKo hK hU
  | succ j ih =>
    have hs : ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F),
        IsCompact C ∧ ∀ g X, W.val.val (blockMatrixAt (j + 1) k hr g X) ≠ 0 → X ∈ C := by
      subst r
      exact unequalRankCompactSupport F T n (j + 1) k ψ V π hπ lambda hlambda W
    obtain ⟨C, hC, hs⟩ := hs
    have hr' : r = n + (j + (k + 1) + 1) := by omega
    obtain ⟨W0, hW0⟩ := exists_adjacent_block_integral_coefficient ν n r j k hr hr'
      ψ π hπ.1.1 lambda W C hC hs
    have hcoef (z : ℂ) (a : ℤ) :
        strictSliceCoefficient F hr ψ μ ν W.val (U z) a =
          strictSliceCoefficient F hr' ψ μ ν W0.val (U z) a := by
      rw [strictSliceCoefficient_eq_restrictedIntegral,
        strictSliceCoefficient_eq_restrictedIntegral,
        unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
      have hd : j + 1 + k + 1 = j + (k + 1) + 1 := by omega
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hW0 q.out, hd]
    have hi := ih hr' W0
    intro a z
    have heq : (fun u => strictSliceCoefficient F hr ψ μ ν W.val (U u) a) =
        fun u => strictSliceCoefficient F hr' ψ μ ν W0.val (U u) a :=
      funext fun u => hcoef u a
    rw [heq]
    exact hi a z

end Langlands.AllField.RankinSelberg.DominantRankTransport
