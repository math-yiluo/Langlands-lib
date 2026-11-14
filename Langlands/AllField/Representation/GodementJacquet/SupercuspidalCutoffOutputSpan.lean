import Langlands.Representation.GodementJacquet.SupercuspidalCutoffOutputSpan
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer
/-! # Spanning by integrated conjugate coefficient cutoffs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel compactMatrixSmoothing_pairing conjugateSupercuspidalCutoffGroupTest conjugateSupercuspidalCutoffGroupTest_apply conjugateSupercuspidalCutoffGroupTest_conjugate conjugateSupercuspidalCutoffGroupTest_eq_zero determinantWeight_locallyConstant determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_smoothFunctional_ne_zero generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integratedConjugateSupercuspidalCutoff_conjugate integratedConjugateSupercuspidalCutoff_ne_zero iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel outputSpanGLBorel outputSpanGLMeasurable outputSpanLocalField outputSpanTopology outputSpanValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation smoothingBorel smoothingDisconnected smoothingGLBorel smoothingGLMeasurable smoothingLocalField smoothingMeasurable smoothingT2 smoothingTopology smoothingValuativeRel supercuspidalConjugateMatrixSmoothing supercuspidalConjugateMatrixSmoothing_eq_integratedAction supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalConjugateMatrixSmoothing_pairing supercuspidalCutoffGroupTest supercuspidalCutoffGroupTest_apply supercuspidalCutoffOutputSpan supercuspidalCutoffOutputSpan_apply_mem supercuspidalCutoffOutputSpan_eq_top supercuspidalMatrixSmoothing supercuspidalMatrixSmoothing_apply supercuspidalMatrixSmoothing_fourier_right supercuspidalMatrixSmoothing_fourier_singular supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalMatrixSmoothing_right supercuspidalMatrixSmoothing_singular transferBorel transferDisconnected transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferT2 transferTopology transferValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance outputSpanGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance outputSpanGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- Conjugation transports both entries of the coefficient and preserves the
determinant-unit cutoff. -/
theorem conjugateSupercuspidalCutoffGroupTest_conjugate
    (v : V) (a g : GeneralLinear (m + 1) F) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
        (isSmoothVector_apply a hℓ) (ρ a v) (a * g * a⁻¹) =
      conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g := by
  let T := (⟨⟩ : LocalFieldData F)
  have hnorm : T.determinantNorm (m + 1) (a * g * a⁻¹) =
      T.determinantNorm (m + 1) g := by
    simp only [map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  by_cases hg : T.determinantNorm (m + 1) g = 1
  · simp only [conjugateSupercuspidalCutoffGroupTest_apply,
      supercuspidalCutoffGroupTest_apply]
    rw [supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m)
        ρ hρ (ρ.dual a ℓ) (isSmoothVector_apply a hℓ) (ρ a v)
        ⟨a * g * a⁻¹, hnorm.trans hg⟩,
      supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩]
    congr 1
    change ℓ (ρ a⁻¹ (ρ (a * g * a⁻¹) (ρ a v))) = ℓ (ρ g v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ
        (ρ.dual a ℓ) (isSmoothVector_apply a hℓ) (ρ a v) _ (by simpa [hnorm] using hg),
      conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ ℓ hℓ v g hg]

/-- Haar conjugation symmetry identifies the translated integrated output with
another output from the same family. -/
theorem integratedConjugateSupercuspidalCutoff_conjugate
    (v w : V) (a : GeneralLinear (m + 1) F) :
    Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
          (isSmoothVector_apply a hℓ) (ρ a v)) (ρ a w) =
      ρ a (Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w) := by
  let μ := generalLinearHaar F m
  let f := conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v
  let f' := conjugateSupercuspidalCutoffGroupTest F ρ hρ (ρ.dual a ℓ)
    (isSmoothVector_apply a hℓ) (ρ a v)
  change AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hρ.1.1 f' (ρ a w)) =
    ρ a (AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hρ.1.1 f w))
  rw [← AlgebraicIntegral.integral_linearMap _
    (Hecke.actionIntegrand_finMeasSupp μ ρ hρ.1.1 f w)]
  rw [← AlgebraicIntegral.integral_comp_measurePreserving
    (Hecke.actionIntegrand ρ hρ.1.1 f' (ρ a w))
    (fun g => a * g * a⁻¹) ((generalLinearHaarSymmetries F m).2.2.2 a)]
  congr 1
  ext g
  change f' (a * g * a⁻¹) • ρ (a * g * a⁻¹) (ρ a w) =
    ρ a (f g • ρ g w)
  rw [conjugateSupercuspidalCutoffGroupTest_conjugate F ρ hρ ℓ hℓ]
  simp only [map_smul, ← Module.End.mul_apply, ← map_mul]
  simp [f]

/-- A nonzero coefficient gives a nonzero integrated conjugate-cutoff output:
its evaluation by the same functional is the positive norm-square integral. -/
theorem integratedConjugateSupercuspidalCutoff_ne_zero
    (v : V) (hv : ℓ v ≠ 0) :
    Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v ≠ 0 := by
  let f := supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v
  have hfone : f 1 = ℓ v := by
    change supercuspidalCutoffMatrixTest (⟨⟩ : LocalFieldData F)
      (Nat.succ_pos m) ρ hρ ℓ hℓ v (1 : GeneralLinear (m + 1) F).val = _
    simpa using supercuspidalCutoffMatrixTest_apply (⟨⟩ : LocalFieldData F)
      (Nat.succ_pos m) ρ hρ ℓ hℓ v
      (1 : ((⟨⟩ : LocalFieldData F).determinantNorm (m + 1)).ker)
  have hpos : 0 < ∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F m :=
    (f.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (f.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      (fun _ => sq_nonneg _) (x := 1) (by
        simpa only [Pi.pow_apply, hfone, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hv)
  have heval :
      ℓ (Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v) =
      ∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F m := by
    rw [Hecke.integratedAction_dual]
    apply integral_congr_ae
    filter_upwards [] with g
    by_cases hg : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1
    · have hc : f g = ℓ (ρ g v) :=
        supercuspidalCutoffMatrixTest_apply (⟨⟩ : LocalFieldData F)
          (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩
      change starRingEnd ℂ (f g) * ℓ (ρ g v) = _
      rw [← hc]
      simpa only [Complex.ofReal_pow] using Complex.conj_mul' (f g)
    · have hc : f g = 0 :=
        supercuspidalCutoffMatrixTest_apply_of_not_mem (⟨⟩ : LocalFieldData F)
          (Nat.succ_pos m) ρ hρ ℓ hℓ v g hg
      simp only [conjugateSupercuspidalCutoffGroupTest_apply]
      change starRingEnd ℂ (f g) * ℓ (ρ g v) = _
      simp [hc]
  intro hz
  rw [hz, map_zero, integral_complex_ofReal] at heval
  exact hpos.ne' (Complex.ofReal_eq_zero.mp heval.symm)

omit ℓ hℓ in
/-- The span of all actual compact conjugate-cutoff outputs, allowing every
smooth functional and both representation vectors. -/
def supercuspidalCutoffOutputSpan : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (v w : V),
    Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w = z}

omit ℓ hℓ in
/-- The output span is stable under the full general linear group. -/
theorem supercuspidalCutoffOutputSpan_apply_mem
    (a : GeneralLinear (m + 1) F) (x : V)
    (hx : x ∈ supercuspidalCutoffOutputSpan F ρ hρ) :
    ρ a x ∈ supercuspidalCutoffOutputSpan F ρ hρ := by
  have hle : supercuspidalCutoffOutputSpan F ρ hρ ≤
      (supercuspidalCutoffOutputSpan F ρ hρ).comap (ρ a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, hℓ, v, w, rfl⟩
    exact Submodule.subset_span ⟨ρ.dual a ℓ, isSmoothVector_apply a hℓ,
      ρ a v, ρ a w, integratedConjugateSupercuspidalCutoff_conjugate F ρ hρ ℓ hℓ v w a⟩
  exact hle hx

omit ℓ hℓ in
/-- In an irreducible supercuspidal representation these actual integrated
outputs span every vector. -/
theorem supercuspidalCutoffOutputSpan_eq_top (hi : ρ.IsIrreducible) :
    supercuspidalCutoffOutputSpan F ρ hρ = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := supercuspidalCutoffOutputSpan F ρ hρ
      apply_mem_toSubmodule := by
        intro a x hx
        exact supercuspidalCutoffOutputSpan_apply_mem F ρ hρ a x hx }
  rcases eq_bot_or_eq_top S with hS | hS
  · have hall : ∀ v : V, v = 0 := by
      intro v
      by_contra hv
      obtain ⟨ℓ, hℓ, hℓv⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 v hv
      have hm : Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
          (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) v ∈ S.toSubmodule :=
        Submodule.subset_span ⟨ℓ, hℓ, v, v, rfl⟩
      rw [hS] at hm
      exact integratedConjugateSupercuspidalCutoff_ne_zero F ρ hρ ℓ hℓ v hℓv hm
    apply Submodule.eq_top_iff'.mpr
    intro v
    rw [hall v]
    exact Submodule.zero_mem _
  · exact congrArg Subrepresentation.toSubmodule hS

end Langlands.AllField.GodementJacquet.Padic
