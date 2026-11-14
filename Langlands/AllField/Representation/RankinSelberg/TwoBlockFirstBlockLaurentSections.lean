import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
/-!
# First-block coefficient functions of a two-block section

For an actual lower-induced section `f` of `σ_0 ⊗ σ_1` and functionals `ℓ_0, ℓ_1`, the
scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)` times the
value at `v` of the actual coefficient function of `σ_0` of the vector obtained by
contracting the second tensor factor of `f(g)` with `ℓ_1`. Lower radical translates do
not change these coefficient functions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul tensorContraction_blockTensor_blockPair_one
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

universe uF uW

section Contraction


end Contraction

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}

/-- Contraction against `ℓ_0 ⊗ ℓ_1` after acting by `diag(v, 1)` is `ℓ_0 (σ_0(v) y)`,
where `y` is the contraction of the second factor. -/
theorem tensorContraction_blockTensor_blockPair_one (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (v : GeneralLinear (m 0 + 1) F) (X : PiTensorProduct ℂ W) :
    tensorContraction ell
        ((succBlockShape m h).blockTensor σ (blockPair F (v, 1)) X) =
      ell 0 (σ 0 v (secondContraction (ell 1) X)) := by
  induction X using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod,
      secondContraction_tprod, Fin.prod_univ_two, blockPair_apply_zero, blockPair_apply_one,
      map_one, Module.End.one_apply]
    simp only [map_smul, smul_eq_mul]
    ring
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add, map_add]

/-- The actual lower radical lies in the lower parabolic with trivial Levi projection,
so it leaves every scalar section unchanged. -/
theorem scalarSection_lowerRadical_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) (a : (succBlockShape m h).Levi F) :
    scalarSection ell f (lowerRadical h F Z * g) a = scalarSection ell f g a := by
  let q : (succBlockShape m h).oppositeParabolic F :=
    Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h F)
      ⟨lowerRadical h F Z, lowerRadical_mem h F Z⟩
  have hq : (succBlockShape m h).oppositeLeviProjection F q = 1 := by
    funext i
    apply Units.ext
    ext a b
    rw [BlockShape.oppositeLeviProjection_apply]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · change lowerRadical h F Z ((succBlockShape m h).index 0 a)
        ((succBlockShape m h).index 0 b) = (1 : Matrix _ _ F) a b
      rw [lowerRadical_index_zero_zero, Matrix.one_apply]
    · change lowerRadical h F Z ((succBlockShape m h).index 1 a)
        ((succBlockShape m h).index 1 b) = (1 : Matrix _ _ F) a b
      rw [lowerRadical_index_one_one, Matrix.one_apply]
  have hcov := scalarSection_covariant ell f q hq g a
  rw [map_one, Units.val_one, inv_one, one_mul, mul_one] at hcov
  exact hcov

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

/-- The first-block coefficient function `v ↦ ℓ_0(σ_0(v) y)` of the contracted value
`y = (1 ⊗ ℓ_1) f(g)`, as an element of the actual coefficient image of `σ_0`. -/
def firstBlockCoefficient
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    (coefficientModel (σ 0) (ell 0)).toSubmodule :=
  modelMap (σ 0) (ell 0) (secondContraction (ell 1).val (sectionEval F h σ f g))

theorem firstBlockCoefficient_apply
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (v : GeneralLinear (m 0 + 1) F) :
    (firstBlockCoefficient ell f g).val.val v =
      scalarSection (fun i => (ell i).val) f g (blockPair F (v, 1)) := by
  rw [scalarSection_def, tensorContraction_blockTensor_blockPair_one]
  rfl

/-- Lower radical translates have the same first-block coefficient function. -/
theorem firstBlockCoefficient_lowerRadical_mul
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    firstBlockCoefficient ell f (lowerRadical h F Z * g) =
      firstBlockCoefficient ell f g := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  rw [firstBlockCoefficient_apply, firstBlockCoefficient_apply, scalarSection_lowerRadical_mul]

/-- The scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)`
times the first-block coefficient function at `v`. -/
theorem scalarSection_firstBlockEmbedding_mul
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (v : GeneralLinear (m 0 + 1) F)
    (g : GeneralLinear (t + 1) F) :
    scalarSection (fun i => (ell i).val) f (firstBlockEmbedding h F v * g) 1 =
      (((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h)
          (blockPair F (v, 1)) : ℂˣ) : ℂ)⁻¹ *
        (firstBlockCoefficient ell f g).val.val v := by
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F (blockPair F (v, 1)))
    (BlockShape.oppositeLeviProjection_section _ _ _) g 1
  rw [one_mul] at hcov
  rw [firstBlockCoefficient_apply]
  exact hcov

open scoped NNReal in
/-- The inverse half modulus of `diag(v, 1)` is the determinant weight `|det v|^(-b/2)`. -/
theorem inv_leviHalfModulus_blockPair_one (v : GeneralLinear (m 0 + 1) F) :
    (((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h)
        (blockPair F (v, 1)) : ℂˣ) : ℂ)⁻¹ =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
        (-(((m 1 + 1 : ℕ) : ℂ) / 2)) := by
  set T := (⟨⟩ : LocalFieldData F)
  set r : ℝ := T.normalizedAbs (GeneralLinear.determinant v : F) with hr_def
  have hr : 0 < r := T.normalizedAbs_pos (GeneralLinear.determinant v).ne_zero
  have hlm : ((T.leviModulus (succBlockShape m h) (blockPair F (v, 1)) : ℝ≥0) : ℝ) =
      r ^ (m 1 + 1) := by
    rw [T.leviModulus_apply]
    simp only [Finset.prod_filter, Fin.prod_univ_two]
    simp only [Fin.isValue, lt_self_iff_false, ite_false, Fin.zero_lt_one, ite_true,
      not_lt_zero, mul_one, one_mul]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow]
    change ((T.determinantNorm (m 0 + 1) (blockPair F (v, 1) 0) : ℝ≥0) : ℝ) ^ (m 1 + 1) /
      ((T.determinantNorm (m 1 + 1) (blockPair F (v, 1) 1) : ℝ≥0) : ℝ) ^ (m 0 + 1) = _
    rw [blockPair_apply_zero, blockPair_apply_one, map_one, Units.val_one, NNReal.coe_one,
      one_pow, div_one]
    rfl
  have hsqrt : Real.sqrt (r ^ (m 1 + 1)) = r ^ ((((m 1 + 1 : ℕ) : ℝ)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [T.leviHalfModulus_apply, Real.coe_sqrt, hlm, hsqrt, determinantWeight]
  change ((r ^ ((((m 1 + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ)⁻¹ = (r : ℂ) ^ (-(((m 1 + 1 : ℕ) : ℂ) / 2))
  rw [← Complex.ofReal_inv, ← Real.rpow_neg hr.le, Complex.ofReal_cpow hr.le]
  push_cast
  ring_nf

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
