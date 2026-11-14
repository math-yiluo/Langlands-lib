import Langlands.Representation.GodementJacquet.SupercuspidalMonomialOutputs
import Langlands.AllField.Representation.GodementJacquet.FourierRegularMatrixTranslates
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator
/-! # Cyclic monomial outputs of Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_smoothFunctional_ne_zero fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMonomialOutputs instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 leftRightTranslate_mem_fourierRegularMatrixTests matrixIntegral matrixIntegrand matrixRationalValues monomialBorel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance monomialT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance monomialDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance monomialMeasurable : MeasurableSpace F := borel _
local instance monomialBorel : BorelSpace F := ⟨rfl⟩
local instance monomialGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance monomialGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The exact determinant factor for the weighted left translate. -/
theorem weightedRegularMatrixTest_leftTranslate
    (a : GeneralLinear (n + 1) F) (s : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1)) :
    weightedRegularMatrixTest F s (regularMatrixTranslate a⁻¹ 1 Φ) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a s •
        Hecke.TestFunction.leftTranslate a (weightedRegularMatrixTest F s Φ) := by
  apply Hecke.TestFunction.ext
  intro g
  have hw := determinantWeight_mul
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a (a⁻¹ * g) s
  simp only [mul_inv_cancel_left] at hw
  simp only [weightedRegularMatrixTest_apply, regularMatrixTranslate_apply,
    Units.val_one, Matrix.mul_one]
  change Φ.val (a⁻¹.val * g.val) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s =
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a s *
      (Φ.val (a⁻¹.val * g.val) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (a⁻¹ * g) s)
  rw [hw]
  ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Left translation acts on the actual operator output by the representation
and its determinant weight. -/
theorem regularMatrixZetaOperator_leftTranslate
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (a : GeneralLinear (n + 1) F) (s : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1)) (v : V) :
    regularMatrixZetaOperator F ρ hρ s (regularMatrixTranslate a⁻¹ 1 Φ) v =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a s •
        ρ a (regularMatrixZetaOperator F ρ hρ s Φ v) := by
  change Hecke.integratedAction (generalLinearHaar F n) ρ hρ
      (weightedRegularMatrixTest F s (regularMatrixTranslate a⁻¹ 1 Φ)) v = _
  rw [weightedRegularMatrixTest_leftTranslate, map_smul, LinearMap.smul_apply,
    Hecke.integratedAction_leftTranslate]
  rfl

/-- A regular test supported on determinant norm one gives an operator
independent of the complex exponent. -/
theorem regularMatrixZetaOperator_eq_of_detNorm_support
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ)
    (Φ : regularMatrixTests (K := F) (n + 1))
    (hΦ : ∀ g : GeneralLinear (n + 1) F,
      (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g ≠ 1 → Φ.val g.val = 0)
    (s t : ℂ) :
    regularMatrixZetaOperator F ρ hρ s Φ = regularMatrixZetaOperator F ρ hρ t Φ := by
  suffices weightedRegularMatrixTest F s Φ = weightedRegularMatrixTest F t Φ by
    exact congrArg (Hecke.integratedAction (generalLinearHaar F n) ρ hρ) this
  apply Hecke.TestFunction.ext
  intro g
  simp only [weightedRegularMatrixTest_apply]
  by_cases hg : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g = 1
  · have hnorm : (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (Matrix.det g.val) = 1 :=
      congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) hg
    simp [determinantWeight, hnorm]
  · rw [hΦ g hg, zero_mul, zero_mul]

variable {m : ℕ}

/-- For any nonzero smooth pairing, one Fourier-regular test has the same
nonzero output on the chosen vector at every exponent. -/
theorem exists_fourierRegular_constant_output_of_pairing
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : ℓ v ≠ 0) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ u : V,
      u ≠ 0 ∧ ∀ s : ℂ,
        regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v = u := by
  let T := (⟨⟩ : LocalFieldData F)
  let C := supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v
  have hC : C ∈ fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests
      T hm ψ ν hsd ρ hρ ℓ hℓ v
  let Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    ⟨conjugateMatrixTest (m + 1) C,
      conjugate_mem_fourierRegularMatrixTests (m + 1) ψ ν hsd hC⟩
  let Ψ : regularMatrixTests (K := F) (m + 1) := ⟨Φ.val, Φ.property.1⟩
  have hsupport : ∀ g : GeneralLinear (m + 1) F,
      T.determinantNorm (m + 1) g ≠ 1 → Ψ.val g.val = 0 := by
    intro g hg
    change starRingEnd ℂ (C g.val) = 0
    rw [show C g.val = 0 from
      supercuspidalCutoffMatrixTest_apply_of_not_mem T (Nat.succ_pos m)
        ρ hρ ℓ hℓ v g hg, map_zero]
  let u := regularMatrixZetaOperator F ρ hρ.1.1 0 Ψ v
  refine ⟨Φ, u, ?_, fun s => ?_⟩
  · let f : GeneralLinear (m + 1) F → ℂ := fun g => C g.val
    have hf : Continuous f := C.continuous.comp Units.continuous_val
    have hfc : HasCompactSupport f :=
      hasCompactSupport_restrict_of_mem_regularMatrixTests (m + 1) hC.1
    have hfone : f 1 = ℓ v := by
      change C (1 : GeneralLinear (m + 1) F).val = _
      have he := supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v
        (1 : (T.determinantNorm (m + 1)).ker)
      simpa [C] using he
    have hpos : 0 < ∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F m :=
      (hf.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
        (fun g => sq_nonneg _) (x := 1) (by
          simpa only [Pi.pow_apply, hfone, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hv)
    have hi : matrixIntegral F Φ.val 0 (fun g => ℓ (ρ g v)) =
        ∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F m := by
      apply integral_congr_ae
      filter_upwards [] with g
      change starRingEnd ℂ (C g.val) * ℓ (ρ g v) *
        determinantWeight (normalizedAbsoluteValue T) g 0 = _
      by_cases hg : T.determinantNorm (m + 1) g = 1
      · have hc : C g.val = ℓ (ρ g v) :=
          supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩
        rw [determinantWeight, Complex.cpow_zero, mul_one, ← hc]
        simpa only [Complex.ofReal_pow] using Complex.conj_mul' (C g.val)
      · have hc : C g.val = 0 :=
          supercuspidalCutoffMatrixTest_apply_of_not_mem T (Nat.succ_pos m)
            ρ hρ ℓ hℓ v g hg
        simp [hc, f]
    intro hu
    have hz : (∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F m) = 0 := by
      rw [← hi, ← regularMatrixZetaOperator_dual F ρ hρ.1.1 0 Ψ v ℓ]
      change ℓ u = 0
      rw [hu, map_zero]
    rw [integral_complex_ofReal] at hz
    exact hpos.ne' (Complex.ofReal_eq_zero.mp hz)
  · exact congrArg (fun A : Module.End ℂ V => A v)
      (regularMatrixZetaOperator_eq_of_detNorm_support F ρ hρ.1.1 Ψ hsupport s 0)

/-- Smooth dual separation supplies the nonzero pairing for every nonzero input
vector, retaining that same input in all the resulting operator evaluations. -/
theorem exists_fourierRegular_constant_output
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : v ≠ 0) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ u : V,
      u ≠ 0 ∧ ∀ s : ℂ,
        regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v = u := by
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 v hv
  exact exists_fourierRegular_constant_output_of_pairing F hm ρ hρ ℓ hℓ ψ ν hsd v hℓv

/-- Outputs on one fixed input that are realized by an actual Fourier-regular
test at every exponent, up to one integer spectral power. -/
def fourierRegularMonomialOutputs
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (v : V) : Set V :=
  {u | ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ k : ℤ, ∀ s : ℂ,
    regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ v =
      spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ k • u}

/-- Translating a realizing test realizes the translated output with the sum
of its old exponent and the determinant order of the translating element. -/
theorem representation_mem_fourierRegularMonomialOutputs
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (v u : V)
    (hu : u ∈ fourierRegularMonomialOutputs F ρ hρ ψ ν hsd v)
    (a : GeneralLinear (m + 1) F) :
    ρ a u ∈ fourierRegularMonomialOutputs F ρ hρ ψ ν hsd v := by
  obtain ⟨Φ, k, hΦ⟩ := hu
  refine ⟨fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ,
    (⟨⟩ : LocalFieldData F).ord (Matrix.det a.val) + k, ?_⟩
  intro s
  change regularMatrixZetaOperator F ρ hρ s
    (regularMatrixTranslate a⁻¹ 1 ⟨Φ.val, Φ.property.1⟩) v = _
  rw [regularMatrixZetaOperator_leftTranslate, hΦ,
    normalizedDeterminantWeight_eq_spectralPoint_zpow, map_smul, smul_smul,
    zpow_add₀ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)]

/-- For a nonzero fixed input in an irreducible supercuspidal representation
of rank at least two, the monomial outputs span the whole carrier. -/
theorem span_fourierRegularMonomialOutputs_eq_top
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v) = ⊤ := by
  obtain ⟨Φ, u, hu, hΦ⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv
  have hmem : u ∈ fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v :=
    ⟨Φ, 0, by simpa only [zpow_zero, one_smul] using hΦ⟩
  apply top_unique
  rw [← span_range_orbit_eq_top hi hu]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact representation_mem_fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v u hmem a

end Langlands.AllField.GodementJacquet.Padic
