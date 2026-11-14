import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentFourier
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections
/-!
# The two large integrands on the first-block fibers

On the fiber `[diag(v, 1) R(y; x) g]` the upper integrand is the actual unequal-rank
integrand at `s = 0` of the right translate of the test function by `R(0; x) g` and the
first-block coefficient function of `f(g)`, times `Φ((x, η) g)`. On the fiber
`[diag(v, 1) g]` the lower integrand is the corresponding inverse half modulus times the
partial Fourier value. At the reflected point `[w v^ι]`, the transformed small integrand
of the translate by `R(0; x) g` is `ψ((x v⁻¹)_0)` times the block-rotated test value.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_reflectionQuotient firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one lowerIntegrand_firstBlockFiberPoint measurePreserving_reflectionQuotient partialSection_firstBlockEmbedding_mul reflectionQuotient_mem_determinantSlice scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul setIntegral_determinantSlice_reflectionQuotient tensorContraction_blockTensor_blockPair_one upperIntegrand_fiberPoint_rowSnoc whittaker_blockRotation_firstBlockEmbedding_lowerRadical
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

universe uF uW

variable {F : Type uF} [Field F]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {m : Fin 2 → ℕ}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

section Character

variable {t : ℕ} {h : ∑ i, (m i + 1) = t + 1}

/-- `W(C diag(v, 1) R(0; x) g) = ψ((x v⁻¹)_0) W(C diag(v, 1) g)`. -/
theorem whittaker_blockRotation_firstBlockEmbedding_lowerRadical
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
    (v : GeneralLinear (m 0 + 1) F) (x : Fin (m 0 + 1) → F)
    (g : GeneralLinear (t + 1) F) :
    Wtest.val (blockRotation h F *
        (firstBlockEmbedding h F v * (lowerRadical h F (rowSnoc 0 x) * g))) =
      ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
        Wtest.val (blockRotation h F * (firstBlockEmbedding h F v * g)) := by
  let u : lowerBlockUnipotent h F :=
    ⟨lowerRadical h F (rowSnoc 0 x * (v⁻¹ : GeneralLinear _ F).val),
      lowerRadical_mem h F _⟩
  have hmul : firstBlockEmbedding h F v * (lowerRadical h F (rowSnoc 0 x) * g) =
      u.val * (firstBlockEmbedding h F v * g) := by
    rw [← mul_assoc, firstBlockEmbedding_mul_lowerRadical, mul_assoc]
  have hdiag : ∀ i, diagonalBlocks h F u i = 1 := by
    intro i
    apply Subtype.ext
    apply Units.ext
    ext a b
    rw [diagonalBlocks_apply]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · exact lowerRadical_index_zero_zero h F _ a b
    · exact lowerRadical_index_one_one h F _ a b
  rw [hmul, Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.whittaker_blockRotation_lowerBlockUnipotent_mul,
    lowerCharacter_eq_diagonalBlocks, hdiag 0, hdiag 1, map_one, map_one, Units.val_one,
    one_mul, one_mul]
  congr 2
  change lowerRadical h F _ ((succBlockShape m h).index 1 (Fin.last (m 1)))
    ((succBlockShape m h).index 0 0) = _
  rw [lowerRadical_index_one_zero, Matrix.mul_apply, rowSnoc_last]
  rfl

end Character

section Upper

variable (h : ∑ i, (m i + 1) = m 0 + (m 1 + 0 + 1) + 1)

/-- On the fiber `[diag(v, 1) R(y; x) g]`, the upper integrand is the actual unequal-rank
integrand at `s = 0` of the translate of the test function by `R(0; x) g` and the
first-block coefficient function of `f(g)`, times `Φ((x, η) g)`. -/
theorem upperIntegrand_fiberPoint_rowSnoc
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ (m 0 + (m 1 + 0 + 1)))
    (Φ : SchwartzBruhat (Fin (m 0 + (m 1 + 0 + 1) + 1) → F))
    (v : GeneralLinear (m 0 + 1) F) (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) F)
    (x : Fin (m 0 + 1) → F) (g : GeneralLinear (m 0 + (m 1 + 0 + 1) + 1) F) :
    Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
        (fiberPoint h F (Quotient.mk _ v) (lowerRadical h F (rowSnoc y x) * g)) =
      unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (m 1) 0
          (translateWhittaker ψ (m 0 + (m 1 + 0 + 1)) Wtest
            (lowerRadical h F (rowSnoc 0 x) * g))
          (firstBlockCoefficient ell f g).val 0 y (Quotient.mk _ v) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) := by
  rw [fiberPoint_mk, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_mk, scalarSection_firstBlockEmbedding_mul,
    firstBlockCoefficient_lowerRadical_mul, inv_leviHalfModulus_blockPair_one,
    lastRow_firstBlockEmbedding_lowerRadical_mul, rowSnoc_last, unequalRankIntegrand_mk,
    translateWhittaker_apply, ← firstBlockEmbedding_mul_lowerRadical_rowSnoc h,
    lowerRadical_rowSnoc]
  simp only [mul_assoc, Nat.add_zero, zero_sub]
  ring

end Upper

section Lower

variable {t : ℕ} {h : ∑ i, (m i + 1) = t + 1}

/-- On the fiber `[diag(v, 1) g]`, the lower integrand is the block-rotated test value, the
inverse half modulus times the first-block coefficient, and the partial Fourier value. -/
theorem lowerIntegrand_firstBlockFiberPoint
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (μ : letI : MeasurableSpace F := borel F
      AdditiveHaarMeasure F)
    (v : GeneralLinear (m 0 + 1) F) (g : GeneralLinear (t + 1) F) :
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ
        (firstBlockFiberPoint F h (Quotient.mk _ v) g) =
      Wtest.val (blockRotation h F * (firstBlockEmbedding h F v * g)) *
        (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
            (-(((m 1 + 1 : ℕ) : ℂ) / 2)) * (firstBlockCoefficient ell f g).val.val v) *
        ((((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) *
          ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
            Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
            ∂rowMeasure μ (m 0 + 1)) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  rw [firstBlockFiberPoint_mk, Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_mk,
    scalarSection_firstBlockEmbedding_mul, inv_leviHalfModulus_blockPair_one,
    partialSection_firstBlockEmbedding_mul]

end Lower

section Dual

variable (h : ∑ i, (m i + 1) = m 0 + (0 + m 1 + 1) + 1) (hlt : m 0 < m 0 + (0 + m 1 + 1))

/-- At the reflected point `[w v^ι]`, the transformed small integrand is the
block-rotated value `W(C diag(v, 1))` times `W'(v)` and the reflected determinant weight. -/
theorem dualIntegrand_reflectionQuotient
    (Wbig : RankinSelberg.WhittakerFunctions ψ (m 0 + (0 + m 1 + 1)))
    (Wsmall : RankinSelberg.InverseWhittakerFunctions ψ (m 0))
    (s : ℂ) (z : Matrix (Fin 0) (Fin (m 0 + 1)) F)
    (v : GeneralLinear (m 0 + 1) F) :
    unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        0 (m 1)
        (translateWhittaker (ψ.scale (-1)) (m 0 + (0 + m 1 + 1))
          (firstDualFunction ψ (m 0 + (0 + m 1 + 1)) Wbig)
          (blockWeylAt (m 0) (m 0 + (0 + m 1 + 1)) hlt))
        (secondDualFunction ψ (m 0) Wsmall) s z (reflectionQuotient (m 0) (Quotient.mk _ v)) =
      Wbig.val (blockRotation h F * firstBlockEmbedding h F v) * Wsmall.val v *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(s - ((0 + m 1 + 1 : ℕ) : ℂ) / 2)) := by
  have hinv : weylLong (m 0 + 1) F * inverseTranspose (m 0 + 1) F
      (weylLong (m 0 + 1) F * inverseTranspose (m 0 + 1) F v) = v := by
    rw [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive, ← mul_assoc,
      weylLong_mul_self, one_mul]
  rw [reflectionQuotient_mk, unequalRankIntegrand_mk, translateWhittaker_apply,
    firstDualFunction_apply, secondDualFunction_apply,
    weylLong_mul_inverseTranspose_dualMatrix h hlt, hinv]
  congr 1
  have hr : 0 < normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det v.val) :=
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos
      ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero
  rw [determinantWeight, determinantWeight, abv_det_weylLong_mul_inverseTranspose,
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg]

end Dual

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
