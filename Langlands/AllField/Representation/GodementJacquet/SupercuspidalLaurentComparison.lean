import Langlands.Representation.GodementJacquet.SupercuspidalLaurentComparison
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalOperatorComparison
/-! # Laurent dependence of a Fourier-regular scalar comparison -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral determinantWeight_sub_spectral exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_regularMatrixZetaOperator_dual_sub exists_laurent_scalar_of_fourierRegular_cross exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaMatrixRationalValues jpssI2 jpssI3 laurentComparisonBorel laurentComparisonDisconnected laurentComparisonGLBorel laurentComparisonGLMeasurable laurentComparisonLocalField laurentComparisonMeasurable laurentComparisonT2 laurentComparisonTopology laurentComparisonValuativeRel leftRightTranslate_mem_fourierRegularMatrixTests matrixIntegral matrixIntegrand matrixRationalValues monomialBorel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance laurentComparisonT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance laurentComparisonDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance laurentComparisonMeasurable : MeasurableSpace F := borel _
local instance laurentComparisonBorel : BorelSpace F := ⟨rfl⟩
local instance laurentComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance laurentComparisonGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The reflected exponent uses the negative determinant order. -/
theorem determinantWeight_sub_spectral
    (g : GeneralLinear (n + 1) F) (t s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (t - s) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g t *
        spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^
          (-(⟨⟩ : LocalFieldData F).ord (Matrix.det g.val)) := by
  rw [show t - s = -s + t by ring, determinantWeight_shift_spectral]
  congr 1
  rw [show spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality (-s) =
      (spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s)⁻¹ by
        simp only [spectralPoint, neg_neg, Complex.cpow_neg, inv_inv], inv_zpow, zpow_neg]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every algebraic evaluation of a regular-test operator at a reflected
parameter is one Laurent polynomial at the original spectral point. -/
theorem exists_laurent_regularMatrixZetaOperator_dual_sub
    (σ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (t : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      ℓ (regularMatrixZetaOperator F σ hσ (t - s) Φ v) =
        laurentEval (spectralUnit
          (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s) A := by
  let T := (⟨⟩ : LocalFieldData F)
  let ord : GeneralLinear (n + 1) F → ℤ :=
    fun g => -T.ord (Matrix.det g.val)
  have hord : Continuous ord :=
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (n + 1)).continuous).neg
  let h : GeneralLinear (n + 1) F → ℂ := fun g =>
    Φ.val g.val * ℓ (σ g v) * determinantWeight (normalizedAbsoluteValue T) g t
  have hh : Continuous h :=
    ((Φ.val.continuous.comp Units.continuous_val).mul
      (((Hecke.orbitMap_locallyConstant σ (hσ v)).comp ℓ).continuous)).mul
      (determinantWeight_locallyConstant F t).continuous
  have hc : HasCompactSupport h :=
    ((hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right).mul_right
  obtain ⟨A, hA⟩ := exists_laurent_integral_discreteWeight
    (generalLinearHaar F n) T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ord hord h hh hc
  refine ⟨A, fun s => ?_⟩
  rw [regularMatrixZetaOperator_dual]
  change (∫ g, Φ.val g.val * ℓ (σ g v) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (t - s)
      ∂generalLinearHaar F n) = _
  simp_rw [determinantWeight_sub_spectral F]
  simpa only [h, ord, T, mul_assoc] using (hA s).2

variable {m : ℕ}

/-- A pointwise scalar comparison with reflected Fourier integrals has one
Laurent scalar valid simultaneously for all tests and all parameters. -/
theorem exists_laurent_scalar_of_fourierRegular_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (σ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hσ : IsSmooth σ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (t : ℂ)
    (hcross : ∀ (s : ℂ) (Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ *
          regularMatrixZetaOperator F σ hσ (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Ψ.val, Ψ.property.2⟩ =
        regularMatrixZetaOperator F σ hσ (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ *
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ A : LaurentCoefficients, ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      regularMatrixZetaOperator F σ hσ (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        laurentEval (spectralUnit
          (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s) A •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F)) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨Φ₀, u, hu, hΦ₀⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv
  obtain ⟨ℓ, _, hℓ⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 u hu
  obtain ⟨B, hB⟩ := exists_laurent_regularMatrixZetaOperator_dual_sub F σ hσ t
    ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ₀.val, Φ₀.property.2⟩ v ℓ
  refine ⟨(ℓ u)⁻¹ • B, fun s => ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_fourierRegularMatrixZetaOperator_cross
    F hm ρ hρ hi ψ ν hsd s
    (fun Φ => regularMatrixZetaOperator F σ hσ (t - s)
      ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩) (hcross s)
  have he := congrArg (fun L : Module.End ℂ V => ℓ (L v)) (hc Φ₀)
  simp only [LinearMap.smul_apply, map_smul, fourierRegularMatrixZetaOperator_apply,
    hΦ₀ s, smul_eq_mul, hB s] at he
  have heval : laurentEval (spectralUnit
      (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
      ((ℓ u)⁻¹ • B) = c := by
    rw [laurentEval_smul, he]
    rw [mul_comm c (ℓ u), inv_mul_cancel_left₀ hℓ]
  intro Φ
  rw [heval]
  exact hc Φ

end Langlands.AllField.GodementJacquet.Padic
