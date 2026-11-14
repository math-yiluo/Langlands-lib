import Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-! Local constancy and measurability of the actual Section 4.7 lower integrand. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding coefficient_locallyConstant groupIntegrand groupIntegrand_def groupIntegrand_locallyConstant groupIntegrand_lowerBlockUnipotent_mul integrand integrand_continuous integrand_locallyConstant integrand_measurable integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_locallyConstant partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_locallyConstant scalarSection_lowerBlockUnipotent_mul sectionEval_locallyConstant sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet hiding integrand
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uV uW

section PartialSection

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F]
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)
variable (μ : AdditiveHaarMeasure F)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- Local constancy of the complete row-translate family passes through the fixed
first-block Fourier integral, for the supplied additive Haar measure. -/
theorem partialSection_locallyConstant :
    IsLocallyConstant (partialSection h ψ μ Φ) := by
  let := isTopologicalRing_carrier F
  have hΦ := (rowTranslate_locallyConstant Φ).comp
    (fun Ψ : (Fin (t + 1) → F) → ℂ =>
      ∫ w, ψ.complex (w 0) *
        Ψ (join (succBlockEquiv h) w (eta (m 1))) ∂rowMeasure μ (m 0 + 1))
  simpa only [Function.comp_def, ← partialSection_apply] using hΦ

end PartialSection

section Sections

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}

/-- Evaluation of an actual smooth opposite-parabolic section is locally constant.
The tensor carrier needs no topology. -/
theorem sectionEval_locallyConstant [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h σ) :
    IsLocallyConstant (sectionEval F h σ f) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set (GeneralLinear (t + 1) F)),
    isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (fun f' => f'.val x) (hK ⟨k, hk⟩)

/-- Every fixed block contraction of a smooth section is locally constant in the
ambient group coordinate. In particular, this applies at the Levi identity. -/
theorem scalarSection_locallyConstant [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (f : Sections F h σ) (a : (succBlockShape m h).Levi F) :
    IsLocallyConstant (fun g => scalarSection ell f g a) := by
  exact (sectionEval_locallyConstant f).comp
    (fun v => tensorContraction ell ((succBlockShape m h).blockTensor σ a v))

end Sections

section Integrand

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : UnitaryAdditiveCharacter F}
variable [MeasurableSpace F]
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GeneralLinear (t + 1) F) V)
variable (hπ : IsSmooth π)
variable (lambda : glFunctionals ψ t π)
variable (Wtest : (coefficientModel π lambda).toSubmodule)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))
variable (μ : AdditiveHaarMeasure F)

include hπ

omit [MeasurableSpace F] in
/-- Actual coefficient-image functions of a smooth representation are locally
constant as scalar functions on the group. -/
theorem coefficient_locallyConstant :
    IsLocallyConstant Wtest.val.val := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  have hc := (Hecke.orbitMap_locallyConstant _ (model_isSmooth π hπ lambda Wtest)).comp
    (fun w : (coefficientModel π lambda).toSubmodule => w.val.val 1)
  change IsLocallyConstant (fun g => Wtest.val.val (1 * g)) at hc
  simpa only [one_mul] using hc

/-- The actual group integrand is locally constant. Smoothness of the test
representation is sufficient; no growth or convergence premise is used. -/
theorem groupIntegrand_locallyConstant :
    IsLocallyConstant (groupIntegrand ell f Wtest.val Φ μ) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  have hW := (coefficient_locallyConstant π hπ lambda Wtest).comp_continuous
    (continuous_const.mul continuous_id :
      Continuous (fun g : GeneralLinear (t + 1) F =>
        blockRotation h F * g))
  exact (hW.comp₂ (scalarSection_locallyConstant (fun i => (ell i).val) f 1) (· * ·)).comp₂
    (partialSection_locallyConstant h ψ μ Φ) (· * ·)

variable [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]

/-- Local constancy descends to the actual lower quotient using its quotient
topology and the proved representative-independent integrand. -/
theorem integrand_locallyConstant :
    IsLocallyConstant (integrand ell f Wtest.val Φ μ) := by
  change IsLocallyConstant (integrand ell f Wtest.val Φ μ)
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.rightRel (lowerBlockUnipotent h F))).isCoinducing.isOpen_preimage.mp
  exact groupIntegrand_locallyConstant ell f π hπ lambda Wtest Φ μ s

/-- The descended lower integrand is continuous. -/
theorem integrand_continuous :
    Continuous (integrand ell f Wtest.val Φ μ) := by
  exact (integrand_locallyConstant ell f π hπ lambda Wtest Φ μ).continuous

/-- Borel measurability of the exact Section 4.7 lower integrand for every
supplied section, coefficient, row test and additive Fourier Haar measure. -/
theorem integrand_measurable
    [MeasurableSpace (LowerQuotient h F)]
    [@BorelSpace (LowerQuotient h F)
      (by infer_instance) _] :
    Measurable (integrand ell f Wtest.val Φ μ) := by
  exact (integrand_continuous ell f π hπ lambda Wtest Φ μ).measurable

end Integrand

end Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
