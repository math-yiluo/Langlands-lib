import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels
/-!
# Compact finiteness of the actual lower mixed fiber kernels
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_lowerMixedFirstQuotient continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint continuous_rightRadicalCoord determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockFiberPoint_slice_isCompact_preimage firstBlockKernel firstBlockKernel_compact_ne_top firstBlockKernel_isSFinite firstBlockKernel_mk instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceLowerQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceMixedQuotient_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceLowerQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceMixedQuotient_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedFirstQuotient lowerMixedFirstQuotient_lower_mul lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_isCompact_preimage radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalKernel radicalKernel_compact_ne_top radicalKernel_isSFinite radicalKernel_mk rightRadicalCoord rightRadicalCoord_mixed_mul_radical
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory Set
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance : MeasurableSpace (LowerQuotient h F) := borel _
local instance : BorelSpace (LowerQuotient h F) := ⟨rfl⟩
local instance : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

/-- The right radical coordinate of a lower mixed matrix. -/
def rightRadicalCoord (l : lowerMixedSubgroup F h) :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F :=
  (((lowerMixedCoordinates F h l).2.2.val)⁻¹).val * entryBlock h F l.val 1 0

theorem continuous_rightRadicalCoord : Continuous (rightRadicalCoord F h) := by
  have hd := (continuous_snd.comp (continuous_snd.comp
    (lowerMixedSubgroupHomeomorph F h).continuous_invFun))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp hd).inv).matrix_mul
    ((continuous_entryBlock h F 1 0).comp continuous_subtype_val)

/-- The coordinate recovers the radical after any diagonal mixed factor. -/
theorem rightRadicalCoord_mixed_mul_radical (b : mixedSubgroup F h)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) :
    rightRadicalCoord F h
      ⟨b.val * lowerRadical h F Z,
        mul_mem (mixedSubgroup_le_lowerMixedSubgroup F h b.property)
          (lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F Z))⟩ = Z := by
  rcases b with ⟨b, ⟨d, rfl⟩⟩
  have he : (⟨mixedEmbedding F h d * lowerRadical h F Z,
      mul_mem (mixedSubgroup_le_lowerMixedSubgroup F h ⟨d, rfl⟩)
        (lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F Z))⟩ :
      lowerMixedSubgroup F h) =
      lowerMixedSubgroupEquiv F h (d.2.val.val * Z * (d.1.val⁻¹).val, d) :=
    Subtype.ext (leviEmbedding_blockPair_mul_lowerRadical h F d.1.val d.2.val Z)
  rw [he]
  change (((lowerMixedDiagonal F h ⟨lowerProduct h F
    (d.2.val.val * Z * (d.1.val⁻¹).val) d.1.val d.2.val, _⟩).2.val)⁻¹).val *
    entryBlock h F
      (lowerProduct h F (d.2.val.val * Z * (d.1.val⁻¹).val) d.1.val d.2.val) 1 0 = Z
  rw [lowerMixedDiagonal_lowerProduct, entryBlock_lowerProduct_one_zero]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- Radical fibers have compact preimages of compact sets in the mixed quotient. -/
theorem radicalFiberPoint_isCompact_preimage (g : GeneralLinear (t + 1) F)
    {S : Set (MixedQuotient F h)} (hS : IsCompact S) :
    IsCompact ((fun Z => radicalFiberPoint F h Z g) ⁻¹' S) :=
  quotientFiber_isCompact_preimage_of_coordinate
    (mixedSubgroup F h) (lowerMixedSubgroup F h)
    (isClosed_mixedSubgroup F h) (isClosed_lowerMixedSubgroup F h)
    (mixedSubgroup_le_lowerMixedSubgroup F h) (lowerRadical h F)
    (continuous_lowerRadical h F)
    (fun Z => lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F Z))
    (rightRadicalCoord F h) (continuous_rightRadicalCoord F h)
    (rightRadicalCoord_mixed_mul_radical F h) g hS

/-- The small quotient of the first diagonal coordinate. -/
def lowerMixedFirstQuotient (l : lowerMixedSubgroup F h) :
    LeftUnipotentQuotient (m 0) F :=
  Quotient.mk _ ((lowerMixedSubgroupEquiv F h).symm l).2.1.val

theorem continuous_lowerMixedFirstQuotient : Continuous (lowerMixedFirstQuotient F h) :=
  continuous_quotient_mk'.comp (continuous_subtype_val.comp
    (continuous_fst.comp (continuous_snd.comp (lowerMixedSubgroupHomeomorph F h).continuous_invFun)))

/-- Multiplication from the lower unipotent subgroup leaves the first quotient unchanged. -/
theorem lowerMixedFirstQuotient_lower_mul (b : lowerBlockUnipotent h F)
    (u : normOneSubgroup F (m 0 + 1)) :
    lowerMixedFirstQuotient F h
      ⟨b.val * firstBlockEmbedding h F u.val,
        mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h b.property)
          (mixedSubgroup_le_lowerMixedSubgroup F h
            (firstBlockEmbedding_mem_mixedSubgroup F h u))⟩ = Quotient.mk _ u.val := by
  have he : ((lowerMixedSubgroupEquiv F h).symm
      ⟨b.val * firstBlockEmbedding h F u.val,
        mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h b.property)
          (mixedSubgroup_le_lowerMixedSubgroup F h
            (firstBlockEmbedding_mem_mixedSubgroup F h u))⟩).2.1.val =
      (diagonalBlocks h F b 0).val * u.val := by
    apply Units.ext
    rw [lowerMixedSubgroupEquiv_symm_apply_fst, Units.val_mul,
      entryBlock_mul, firstBlockEmbedding_apply]
    simp only [entryBlock_levi_zero_zero, entryBlock_levi_one_zero,
      Matrix.mul_zero, add_zero]
    rfl
  unfold lowerMixedFirstQuotient
  rw [he]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
    (diagonalBlocks h F b 0).property u.val

/-- First-block fibers restricted to one determinant slice have compact preimages. -/
theorem firstBlockFiberPoint_slice_isCompact_preimage (k : ℤ)
    (g : GeneralLinear (t + 1) F)
    {S : Set (LowerQuotient h F)} (hS : IsCompact S) :
    IsCompact (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k ∩
      (fun q => firstBlockFiberPoint F h q g) ⁻¹' S) := by
  classical
  let H := lowerBlockUnipotent h F
  let L := lowerMixedSubgroup F h
  let := leftQuotient_t2Space H (isClosed_lowerBlockUnipotent_canonical F h)
  let B := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k ∩
    (fun q => firstBlockFiberPoint F h q g) ⁻¹' S
  by_cases hB : B.Nonempty
  · obtain ⟨q0, hq0⟩ := hB
    induction q0 using Quotient.inductionOn with
    | h u0 =>
      obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H
        (isClosed_lowerBlockUnipotent_canonical F h) hS
      let D : Set L := Subtype.val ⁻¹'
        ((fun c => c * g⁻¹ * (firstBlockEmbedding h F u0)⁻¹) '' C)
      have hD : IsCompact D :=
        (isClosed_lowerMixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
          (hC.image ((continuous_id.mul continuous_const).mul continuous_const))
      let ψ : L → LeftUnipotentQuotient (m 0) F :=
        fun l => rightTranslate _ u0 (lowerMixedFirstQuotient F h l)
      have hψ : Continuous ψ :=
        (rightTranslate _ u0).continuous.comp (continuous_lowerMixedFirstQuotient F h)
      have hf : Continuous (fun q => firstBlockFiberPoint F h q g) :=
        (continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)
      apply (hD.image hψ).of_isClosed_subset
        ((Langlands.AllField.RankinSelberg.isClosed_determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k).inter
          (hS.isClosed.preimage hf))
      intro q hq
      induction q using Quotient.inductionOn with
      | h u =>
        have huv : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant u : F) =
            (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant u0 : F) :=
          hq.1.trans hq0.1.symm
        let v : normOneSubgroup F (m 0 + 1) :=
          ⟨u * u0⁻¹, mul_inv_mem_normOne_of_ord_eq F u u0 huv⟩
        have hxC : firstBlockFiberPoint F h (Quotient.mk _ u) g ∈ leftQuotientMap H '' C := by
          rw [hCS]
          exact hq.2
        obtain ⟨c, hc, hcu⟩ := hxC
        have hb : c * (firstBlockEmbedding h F u * g)⁻¹ ∈ H :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact hcu.symm)
        let b : H := ⟨c * (firstBlockEmbedding h F u * g)⁻¹, hb⟩
        have he : c * g⁻¹ * (firstBlockEmbedding h F u0)⁻¹ =
            b.val * firstBlockEmbedding h F v.val := by
          dsimp [b, v]
          simp only [map_mul, map_inv, mul_inv_rev]
          group
        let l : L := ⟨b.val * firstBlockEmbedding h F v.val,
          mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h hb)
            (mixedSubgroup_le_lowerMixedSubgroup F h
              (firstBlockEmbedding_mem_mixedSubgroup F h v))⟩
        refine ⟨l, ⟨c, hc, he⟩, ?_⟩
        change rightTranslate _ u0 (lowerMixedFirstQuotient F h l) = Quotient.mk _ u
        rw [lowerMixedFirstQuotient_lower_mul F h b v, rightTranslate_mk]
        simp [v, mul_assoc]
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    change IsCompact B
    rw [he]
    exact isCompact_empty

section RadicalKernel

variable (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))
  [μR.IsAddHaarMeasure]

/-- Every radical kernel measure is finite on compact sets. -/
theorem radicalKernel_compact_ne_top (q : LowerMixedQuotient F h)
    (S : Set (MixedQuotient F h)) (hS : IsCompact S) :
    radicalKernel F h μR q S ≠ ⊤ := by
  let := leftQuotient_t2Space (mixedSubgroup F h) (isClosed_mixedSubgroup F h)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun Z => radicalFiberPoint F h Z g) :=
      ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [radicalKernel_mk F h μR g, Measure.map_apply hf hS.measurableSet]
    exact (radicalFiberPoint_isCompact_preimage F h g hS).measure_ne_top

/-- Compact finiteness on a common countable compact cover gives radical kernel s-finiteness. -/
theorem radicalKernel_isSFinite : IsSFiniteKernel (radicalKernel F h μR) := by
  let H := mixedSubgroup F h
  let := leftQuotient_t2Space H (isClosed_mixedSubgroup F h)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (radicalKernel F h μR)
    (radicalKernel_compact_ne_top F h μR)

end RadicalKernel

section FirstBlockKernel

variable (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
  [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)

/-- Every first-block slice kernel measure is finite on compact sets. -/
theorem firstBlockKernel_compact_ne_top (k : ℤ) (q : LowerMixedQuotient F h)
    (S : Set (LowerQuotient h F)) (hS : IsCompact S) :
    firstBlockKernel F h νA hνA k q S ≠ ⊤ := by
  let := leftQuotient_t2Space (lowerBlockUnipotent h F)
    (isClosed_lowerBlockUnipotent_canonical F h)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun q => firstBlockFiberPoint F h q g) :=
      ((continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockKernel_mk F h νA hνA k g, Measure.map_apply hf hS.measurableSet,
      Measure.restrict_apply (hf hS.measurableSet), Set.inter_comm]
    exact (firstBlockFiberPoint_slice_isCompact_preimage F h k g hS).measure_ne_top

/-- Compact finiteness on a common countable compact cover gives first-block kernel s-finiteness. -/
theorem firstBlockKernel_isSFinite (k : ℤ) :
    IsSFiniteKernel (firstBlockKernel F h νA hνA k) := by
  let H := lowerBlockUnipotent h F
  let := leftQuotient_t2Space H (isClosed_lowerBlockUnipotent_canonical F h)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (firstBlockKernel F h νA hνA k)
    (firstBlockKernel_compact_ne_top F h νA hνA k)

end FirstBlockKernel

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
