import Langlands.Representation.GodementJacquet.SupercuspidalOperatorComparison
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMonomialOutputs
/-! # Descending the Fourier-regular operator comparison -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

universe uI uV

variable {I : Type uI} {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaMatrixRationalValues jpssI2 jpssI3 leftRightTranslate_mem_fourierRegularMatrixTests matrixIntegral matrixIntegrand matrixRationalValues monomialBorel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance comparisonT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance comparisonDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance comparisonMeasurable : MeasurableSpace F := borel _
local instance comparisonBorel : BorelSpace F := ⟨rfl⟩

variable {m : ℕ}

/-- Restrict the actual compact zeta operator to Fourier-regular tests. -/
def fourierRegularMatrixZetaOperator
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] Module.End ℂ V :=
  (regularMatrixZetaOperator F ρ hρ s).comp
    (Submodule.inclusion (show fourierRegularMatrixTests (m + 1) ψ ν hsd ≤
      regularMatrixTests (K := F) (m + 1) from inf_le_left))

@[simp] theorem fourierRegularMatrixZetaOperator_apply
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) :
    fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ =
      regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ := rfl

/-- The Fourier-regular operator family has zero common kernel at every
exponent, by the nonzero constant-output witness on a chosen nonzero input. -/
theorem fourierRegularMatrixZetaOperator_separates
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ) (v : V)
    (hv : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ v = 0) :
    v = 0 := by
  by_contra hv0
  obtain ⟨Φ, u, hu, hΦ⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv0
  exact hu ((hΦ s).symm.trans (hv Φ))

/-- At every exponent the finite-output presentation is surjective, because
the monomial outputs on one nonzero input span and spectral powers are nonzero. -/
theorem fourierRegularMatrixZetaOperator_output_surjective
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    Function.Surjective (operatorFamilyLinearCombination
      (fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s)) := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F)) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← span_fourierRegularMonomialOutputs_eq_top F hm ρ hρ hi ψ ν hsd v hv]
  apply Submodule.span_le.mpr
  intro u hu
  obtain ⟨Φ, k, hΦ⟩ := hu
  have hout : fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ v ∈
      LinearMap.range (operatorFamilyLinearCombination
        (fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s)) :=
    ⟨Finsupp.single (Φ, v) 1, operatorFamilyLinearCombination_single _ _ _⟩
  change regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v ∈ _ at hout
  rw [hΦ s] at hout
  exact (Submodule.smul_mem_iff _ (zpow_ne_zero k (spectralPoint_ne_zero_of_pos
    (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s))).mp hout

/-- A comparison that commutes with all Fourier-regular test operators
commutes with the representation, by left translation and output spanning. -/
theorem intertwining_of_commutes_fourierRegularMatrixZetaOperator
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ) (f : Module.End ℂ V)
    (hf : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ * f =
        f * fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (a : GeneralLinear (m + 1) F) :
    f.comp (ρ a) = (ρ a).comp f := by
  let A := fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s
  have ht (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
      A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) w =
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a s •
          ρ a (A Φ w) :=
    regularMatrixZetaOperator_leftTranslate F ρ hρ.1.1 a s
      ⟨Φ.val, Φ.property.1⟩ w
  have hOn (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
      f (ρ a (A Φ w)) = ρ a (f (A Φ w)) := by
    have h := congrArg (fun L : Module.End ℂ V => L w)
      (hf (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ))
    change A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) (f w) =
      f (A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) w) at h
    rw [ht, ht, map_smul] at h
    have hc := smul_right_injective V
      (determinantWeight_ne_zero (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a s) h
    have hfw : A Φ (f w) = f (A Φ w) :=
      congrArg (fun L : Module.End ℂ V => L w) (hf Φ)
    rw [hfw] at hc
    exact hc.symm
  have hcomb : (f.comp (ρ a)).comp (operatorFamilyLinearCombination A) =
      ((ρ a).comp f).comp (operatorFamilyLinearCombination A) := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, operatorFamilyLinearCombination,
      Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun w : V => c • w) (hOn j.1 j.2)
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ :=
    fourierRegularMatrixZetaOperator_output_surjective F hm ρ hρ hi ψ ν hsd s v
  exact congrArg (fun L => L x) hcomb

/-- For the actual Fourier-regular operator family, the cross identity
forces any comparison family to be a single scalar multiple at each exponent. -/
theorem exists_scalar_of_fourierRegularMatrixZetaOperator_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (D : fourierRegularMatrixTests (m + 1) ψ ν hsd → Module.End ℂ V)
    (hcross : ∀ Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ * D Ψ =
        D Φ * fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ c : ℂ, ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      D Φ = c • fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let A := fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s
  have hsurj := fourierRegularMatrixZetaOperator_output_surjective F hm ρ hρ hi ψ ν hsd s
  have hsep := fourierRegularMatrixZetaOperator_separates F hm ρ hρ ψ ν hsd s
  let f := operatorFamilyComparison A D hsurj hsep hcross
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := f
      isIntertwining' := fun a =>
        intertwining_of_commutes_fourierRegularMatrixZetaOperator F hm ρ hρ hi ψ ν hsd s f
          (operatorFamilyComparison_commutes A D hsurj hsep hcross) a }
  obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ.1 hi T
  refine ⟨c, fun Φ => ?_⟩
  apply LinearMap.ext
  intro v
  change D Φ v = c • (A Φ v)
  rw [← operatorFamilyComparison_apply_output A D hsurj hsep hcross Φ v]
  exact congrArg (fun L : ρ.IntertwiningMap ρ => L (A Φ v)) hc

end Padic

end Langlands.AllField.GodementJacquet
