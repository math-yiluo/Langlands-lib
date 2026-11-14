import Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Spectral dependence of the actual dominant quotient kernel on each slice

The exact supplied lower measure and the integral of the raw kernel's norm
are retained. All integrability assertions below are equivalences.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff determinantWeight_lowerBlockUnipotent_mul fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelSliceCoefficient kernel_covariance kernel_eq kernel_spectral measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding compatible_measure_data integrable_lowerMeasure_iff integral_lowerMeasure lowerMeasure lowerMeasure_restrict measureTransportFieldT2 measureTransportFieldTopology measureTransportFieldValuation measureTransportGeneralLinearGroup measureTransportGeneralLinearLocallyCompact measureTransportGeneralLinearSecondCountable measureTransportLocalField sigmaFinite_lowerMeasure
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice

universe uF uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance sliceSpectralMeasurable : MeasurableSpace F := borel F

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i+1) = t+1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}
  (ν : AdditiveHaarMeasure F)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)

/-- Changing the parameter changes only the actual determinant weight. -/
theorem kernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) :
    kernel ell f Wtest hr s g x y =
      kernel ell f Wtest hr 0 g x y *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := by
  unfold kernel
  rw [show s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ) =
      (0 - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) + s by ring,
    determinantWeight_exponent_add, mul_assoc]

/-- The complex rectangle integral keeps its spectral weight outside. -/
theorem representativeKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F) :
    representativeKernel ν ell f Wtest hr s g =
      representativeKernel ν ell f Wtest hr 0 g *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := by
  simp only [representativeKernel]
  simp_rw [kernel_spectral ell f Wtest hr s]
  exact integral_mul_const _ _

/-- The real profile is the integral of the raw norm, with its own weight. -/
theorem representativeNormProfile_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F) :
    representativeNormProfile ν ell f Wtest hr s g =
      representativeNormProfile ν ell f Wtest hr 0 g *
        ‖determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s‖ := by
  simp only [representativeNormProfile]
  simp_rw [kernel_spectral ell f Wtest hr s, norm_mul]
  exact integral_mul_const _ _

/-- Fiber integrability is unchanged by the nonzero spectral weight. -/
theorem fiberIntegrable_spectral_iff (hr : r=t+(j+k+1)) (s : ℂ)
    (g : GeneralLinear (t+1) F) :
    FiberIntegrable ν ell f Wtest hr s g ↔
      FiberIntegrable ν ell f Wtest hr 0 g := by
  have hw : determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).ne_zero g.det_ne_zero)))
  simp only [FiberIntegrable]
  simp_rw [kernel_spectral ell f Wtest hr s]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hw) _

/-- Actual spectral dependence after descent, without a representative choice. -/
theorem quotientKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F) :
    quotientKernel ν ell f Wtest hr s q =
      quotientKernel ν ell f Wtest hr 0 q *
        spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientKernel_mk, quotientKernel_mk,
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    change representativeKernel ν ell f Wtest hr s g = _
    rw [representativeKernel_spectral, normalizedDeterminantWeight_eq_spectralPoint_zpow]
    rfl

theorem quotientNormProfile_spectral (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F) :
    quotientNormProfile ν ell f Wtest hr s q =
      quotientNormProfile ν ell f Wtest hr 0 q *
        ‖spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h q‖ := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientNormProfile_mk, quotientNormProfile_mk,
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    change representativeNormProfile ν ell f Wtest hr s g = _
    rw [representativeNormProfile_spectral, normalizedDeterminantWeight_eq_spectralPoint_zpow]
    rfl

theorem quotientFiberIntegrable_spectral_iff (hr : r=t+(j+k+1)) (s : ℂ)
    (q : LowerQuotient h F) :
    quotientFiberIntegrable ν ell f Wtest hr s q ↔
      quotientFiberIntegrable ν ell f Wtest hr 0 q := by
  induction q using Quotient.inductionOn with
  | h g => exact fiberIntegrable_spectral_iff ν ell f Wtest hr s g

section Slices

variable [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
  [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)]

variable (νN : Measure (LeftUnipotentQuotient t F))

/-- The actual zero-parameter coefficient on a lower determinant slice,
with exactly the transported supplied standard quotient measure. -/
def kernelSliceCoefficient (hr : r=t+(j+k+1)) (d : ℤ) : ℂ :=
  ∫ q in Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
    quotientKernel ν ell f Wtest hr 0 q ∂lowerMeasure F h νN

omit [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
  [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)] in
theorem quotientKernel_spectral_onSlice (hr : r=t+(j+k+1)) (s : ℂ)
    (d : ℤ) (q : LowerQuotient h F)
    (hq : q ∈ Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :
    quotientKernel ν ell f Wtest hr s q =
      quotientKernel ν ell f Wtest hr 0 q *
        spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ d := by
  rw [quotientKernel_spectral,
    (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hq]

omit [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
  [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)] in
theorem quotientNormProfile_spectral_onSlice (hr : r=t+(j+k+1)) (s : ℂ)
    (d : ℤ) (q : LowerQuotient h F)
    (hq : q ∈ Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :
    quotientNormProfile ν ell f Wtest hr s q =
      quotientNormProfile ν ell f Wtest hr 0 q *
        ‖spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ d‖ := by
  rw [quotientNormProfile_spectral,
    (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hq]

omit [BorelSpace (LeftUnipotentQuotient t F)] in
/-- The total complex slice integral has the exact coefficient scaling.
This identity does not assert convergence. -/
theorem setIntegral_quotientKernel_spectral (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    (∫ q in Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
      quotientKernel ν ell f Wtest hr s q ∂lowerMeasure F h νN) =
      kernelSliceCoefficient ν ell f Wtest νN hr d *
        spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ d := by
  rw [setIntegral_congr_fun
    (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)
    (fun q hq => quotientKernel_spectral_onSlice ν ell f Wtest hr s d q hq),
    integral_mul_const]
  rfl

omit [BorelSpace (LeftUnipotentQuotient t F)] in
/-- Genuine outer integrability on a single slice is equivalent at `s` and zero. -/
theorem integrableOn_quotientKernel_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    IntegrableOn (quotientKernel ν ell f Wtest hr s)
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) ↔
    IntegrableOn (quotientKernel ν ell f Wtest hr 0)
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) := by
  have hc : spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ d ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
  rw [integrableOn_congr_fun
    (fun q hq => quotientKernel_spectral_onSlice ν ell f Wtest hr s d q hq)
    (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hc) _

omit [BorelSpace (LeftUnipotentQuotient t F)] in
/-- Genuine outer integrability of the raw-norm profile has the same equivalence. -/
theorem integrableOn_quotientNormProfile_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    IntegrableOn (quotientNormProfile ν ell f Wtest hr s)
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) ↔
    IntegrableOn (quotientNormProfile ν ell f Wtest hr 0)
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) (lowerMeasure F h νN) := by
  have hc : spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ d ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
  rw [integrableOn_congr_fun
    (fun q hq => quotientNormProfile_spectral_onSlice ν ell f Wtest hr s d q hq)
    (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h d)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ (norm_ne_zero_iff.mpr hc)) _

omit [BorelSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LowerQuotient h F)] in
/-- The actual fiber condition is equivalent almost everywhere for the exact
restricted lower measure, independently of outer integrability. -/
theorem ae_quotientFiberIntegrable_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    (∀ᵐ q ∂(lowerMeasure F h νN).restrict
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      quotientFiberIntegrable ν ell f Wtest hr s q) ↔
    (∀ᵐ q ∂(lowerMeasure F h νN).restrict
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      quotientFiberIntegrable ν ell f Wtest hr 0 q) :=
  Filter.eventually_congr (Filter.Eventually.of_forall
    (fun q => quotientFiberIntegrable_spectral_iff ν ell f Wtest hr s q))

/-- Package the three genuine convergence equivalences on one slice using
the existing absolute-input predicate and restriction of the supplied measure. -/
theorem kernelAbsoluteIntegrable_restrict_spectral_iff
    (hr : r=t+(j+k+1)) (s : ℂ) (d : ℤ) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s
      (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d)) ↔
    KernelAbsoluteIntegrable ν ell f Wtest hr 0
      (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d)) := by
  simp only [kernelAbsoluteIntegrable_iff, KernelOuterIntegrable, OuterIntegrable,
    KernelNormProfileIntegrable, NormProfileIntegrable]
  have hmeasure :
      lowerMeasure F h
        (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d)) =
      (lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    (lowerMeasure_restrict F h νN d).symm
  rw [hmeasure]
  exact and_congr
    (integrableOn_quotientKernel_spectral_iff ν ell f Wtest νN hr s d)
    (and_congr
      (integrableOn_quotientNormProfile_spectral_iff ν ell f Wtest νN hr s d)
      (ae_quotientFiberIntegrable_spectral_iff ν ell f Wtest νN hr s d))

end Slices

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
