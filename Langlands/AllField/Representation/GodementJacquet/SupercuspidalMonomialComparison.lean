import Langlands.Representation.GodementJacquet.SupercuspidalMonomialComparison
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalLaurentComparison
/-! # Nonzero monomial comparison of Fourier-regular matrix operators -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.Polynomial

end Langlands.AllField.RankinSelberg

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Fourier


end Fourier

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral determinantWeight_sub_spectral exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_regularMatrixZetaOperator_dual_sub exists_laurent_scalar_of_fourierRegular_cross exists_monomial_scalar_of_fourierRegular_cross exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaMatrixRationalValues jpssI2 jpssI3 laurentComparisonBorel laurentComparisonDisconnected laurentComparisonGLBorel laurentComparisonGLMeasurable laurentComparisonLocalField laurentComparisonMeasurable laurentComparisonT2 laurentComparisonTopology laurentComparisonValuativeRel leftRightTranslate_mem_fourierRegularMatrixTests matrixIntegral matrixIntegrand matrixRationalValues monomialBorel monomialComparisonBorel monomialComparisonDisconnected monomialComparisonLocalField monomialComparisonMeasurable monomialComparisonT2 monomialComparisonTopology monomialComparisonValuativeRel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs scalar_ne_zero_of_fourierRegular_comparison span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance monomialComparisonT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance monomialComparisonDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance monomialComparisonMeasurable : MeasurableSpace F := borel _
local instance monomialComparisonBorel : BorelSpace F := ⟨rfl⟩

variable {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A scalar comparison with a supercuspidal Fourier-side family cannot vanish. -/
theorem scalar_ne_zero_of_fourierRegular_comparison [Nontrivial V]
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hσ : GeneralLinear.IsSupercuspidal σ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s t c : ℂ)
    (hc : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      regularMatrixZetaOperator F σ hσ.1.1 (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        c • fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ) : c ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨Ψ, u, hu, hΨ⟩ := exists_fourierRegular_constant_output F hm σ hσ ψ ν hsd v hv
  obtain ⟨Φ, hΦ⟩ := (fourierRegularMatrixFourierEquiv (m + 1) ψ ν hsd).surjective Ψ
  have htest : (⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val,
      Φ.property.2⟩ : regularMatrixTests (K := F) (m + 1)) =
      ⟨Ψ.val, Ψ.property.1⟩ := by
    apply Subtype.ext
    exact congrArg (fun Θ : fourierRegularMatrixTests (m + 1) ψ ν hsd => Θ.val) hΦ
  have he := congrArg (fun L : Module.End ℂ V => L v) (hc Φ)
  rw [htest, hΨ (t - s), hzero, zero_smul, LinearMap.zero_apply] at he
  exact hu he

/-- Supercuspidality on both actual operator sides makes the Laurent comparison
scalar a single nonzero monomial. The analytic cross identity remains explicit. -/
theorem exists_monomial_scalar_of_fourierRegular_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (σ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hσ : GeneralLinear.IsSupercuspidal σ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (t : ℂ)
    (hcross : ∀ (s : ℂ) (Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ *
          regularMatrixZetaOperator F σ hσ.1.1 (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Ψ.val, Ψ.property.2⟩ =
        regularMatrixZetaOperator F σ hσ.1.1 (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ *
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ (c : ℂˣ) (k : ℤ), ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      regularMatrixZetaOperator F σ hσ.1.1 (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        ((c : ℂ) * spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F)) ρ.asModule
  obtain ⟨A, hA⟩ := exists_laurent_scalar_of_fourierRegular_cross
    F hm ρ hρ hi σ hσ.1.1 ψ ν hsd t hcross
  have hne : ∀ x : ℂˣ, laurentEval x A ≠ 0 := by
    intro x
    obtain ⟨s, rfl⟩ := exists_spectralUnit_eq (⟨⟩ : LocalFieldData F).residueCardinality_gt_one x
    exact scalar_ne_zero_of_fourierRegular_comparison F hm ρ hρ.1.1 σ hσ ψ ν hsd s t
      _ (hA s)
  obtain ⟨c, k, hck⟩ := exists_monomial_of_laurentEval_ne_zero A hne
  refine ⟨c, k, fun s Φ => ?_⟩
  simpa only [hck, map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit] using hA s Φ

end Padic
end Langlands.AllField.GodementJacquet
