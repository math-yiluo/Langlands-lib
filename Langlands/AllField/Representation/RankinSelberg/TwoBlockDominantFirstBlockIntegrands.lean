import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockIntegrands
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockCoordinates
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections
/-! # Scalar and Jacobian bridges for the dominant first-block calculation -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical firstBlockFiberIntegrand firstBlockRowJacobian firstBlockUpperValue firstBlockUpperValue_fiber firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation integrable_firstBlockRowChange_iff integral_firstBlockRowChange integral_firstBlockUpperValue integrandBridgeMeasurable integrandBridgeTopology rectangularMeasure_map_firstBlockRowChange unequalRankIntegrandAt_mk
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent

open scoped NNReal

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance integrandBridgeMeasurable : MeasurableSpace F := borel F

theorem unequalRankIntegrandAt_mk {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (W : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (X : Matrix (Fin j) (Fin (n + 1)) F)
    (v : GeneralLinear (n + 1) F) :
    unequalRankIntegrandAt F j k hr ψ abv W W' s X (Quotient.mk _ v) =
      W.val (reindex (finCongr (congrArg (· + 1) hr.symm))
        (unequalRankMatrix j k v X)) * W'.val v *
          determinantWeight abv v (s - ((j + k + 1 : ℕ) : ℂ) / 2) := by
  subst r
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)

variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

/-- The representative scalar after moving the outer rectangle to the left.
Its determinant exponent includes the Jacobian of that first move. -/
def firstBlockUpperValue (s : ℂ) (g : GeneralLinear (t + 1) F)
    (X : Matrix (Fin j) (Fin (t + 1)) F) : ℂ :=
  scalarSection (fun i => (ell i).val) f g 1 *
    Wtest.val (rectangularUnipotent j k X * appendIdentity t (j + k + 1) g) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))

/-- The actual smaller JPSS integrand on the joined rows `Z,T`. -/
def firstBlockFiberIntegrand (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F)
    (T : Matrix (Fin j) (Fin (m 0 + 1)) F) : ℂ :=
  unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (translateWhittaker ψ (t + (j + k + 1)) Wtest
      (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g))
    (firstBlockCoefficient ell f g).val s (firstBlockRows j Z T) (Quotient.mk _ v)

theorem determinantWeight_firstBlockEmbedding (abv : AbsoluteValue F ℝ)
    (v : GeneralLinear (m 0 + 1) F) (s : ℂ) :
    determinantWeight abv (firstBlockEmbedding h F v) s =
      determinantWeight abv v s := by
  change (abv (GeneralLinear.determinant (firstBlockEmbedding h F v) : F) : ℂ) ^ s = _
  rw [determinant_firstBlockEmbedding]
  rfl

theorem determinantWeight_lowerRadical (abv : AbsoluteValue F ℝ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) (s : ℂ) :
    determinantWeight abv (lowerRadical h F Z) s = 1 := by
  change (abv (GeneralLinear.determinant (lowerRadical h F Z) : F) : ℂ) ^ s = 1
  simp only [determinant_lowerRadical, Units.val_one, map_one, Complex.ofReal_one,
    Complex.one_cpow]

/-- The exact supplied-Haar row Jacobian is the negative integral determinant weight. -/
theorem firstBlockRowJacobian (v : GeneralLinear (m 0 + 1) F) :
    ((((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) v : ℝ≥0) ^ j)⁻¹ :
      ℝ≥0) : ℝ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
        (-(j : ℂ)) := by
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

/-- Before the affine substitution, the upper value is the actual smaller
integrand times the external-row determinant power and the base-point weight. -/
theorem firstBlockUpperValue_fiber (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (U : Matrix (Fin j) (Fin (m 0 + 1)) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    firstBlockUpperValue F h j k ell f Wtest s
        (firstBlockEmbedding h F v * (lowerRadical h F Z * g))
        (firstBlockColumns h j U Y) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v (j : ℂ) *
        firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g (U * v.val + Y * Z) := by
  rw [firstBlockUpperValue, firstBlockFiberIntegrand, scalarSection_firstBlockEmbedding_mul,
    firstBlockCoefficient_lowerRadical_mul, inv_leviHalfModulus_blockPair_one,
    unequalRankIntegrandAt_mk, translateWhittaker_apply]
  have hm :
      rectangularUnipotent j k (firstBlockColumns h j U Y) *
          appendIdentity t (j + k + 1)
            (firstBlockEmbedding h F v * (lowerRadical h F Z * g)) =
        firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) *
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g) := by
    simp only [map_mul]
    rw [← mul_assoc, ← mul_assoc, firstBlock_matrix_factorization, mul_assoc]
  rw [hm]
  change _ = _ * _ *
    (Wtest.val (firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) * _) *
      _ * _)
  rw [determinantWeight_mul, determinantWeight_mul, determinantWeight_firstBlockEmbedding,
    determinantWeight_lowerRadical, one_mul]
  have hw :
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (s - ((m 1 + 1 + j + k + 1 : ℕ) : ℂ) / 2) := by
    rw [← determinantWeight_add, ← determinantWeight_add]
    congr 1
    push_cast
    ring
  calc
    _ = (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))) *
        (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
        Wtest.val (firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) *
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g)) *
        (firstBlockCoefficient ell f g).val.val v) := by ring
    _ = _ := by rw [hw]; ring

/-- The affine row substitution cancels the extra external-row determinant
weight, retaining the supplied scalar Haar and the base-point weight. -/
theorem integral_firstBlockUpperValue (ν : AdditiveHaarMeasure F) (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    (∫ U, firstBlockUpperValue F h j k ell f Wtest s
      (firstBlockEmbedding h F v * (lowerRadical h F Z * g))
      (firstBlockColumns h j U Y) ∂rectangularMeasure ν j (m 0 + 1)) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ∫ T, firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g T
        ∂rectangularMeasure ν j (m 0 + 1) := by
  simp_rw [firstBlockUpperValue_fiber]
  rw [integral_const_mul, integral_firstBlockRowChange]
  have hs (z : ℂ) :
      ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) v : ℝ≥0) ^ j)⁻¹ :
        ℝ≥0) • z =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
        (-(j : ℂ)) * z := by
    rw [NNReal.smul_def, Complex.real_smul, firstBlockRowJacobian F j v]
  rw [hs]
  have hc :
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(j : ℂ)) = 1 := by
    rw [← determinantWeight_add]
    simp [determinantWeight]
  calc
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ((determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(j : ℂ))) *
      ∫ T, firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g T
        ∂rectangularMeasure ν j (m 0 + 1)) := by ring
    _ = _ := by rw [hc, one_mul]

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
