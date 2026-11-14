import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
/-!
# Properness on first-block determinant slices
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  borel _
local instance : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

open Set
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

/-- The first block of a mixed element, viewed on the small quotient. -/
def mixedFirstQuotient (l : mixedSubgroup F h) : LeftUnipotentQuotient (m 0) F :=
  Quotient.mk _ ((mixedSubgroupEquiv F h).symm l).1.val

theorem continuous_mixedFirstQuotient : Continuous (mixedFirstQuotient F h) :=
  continuous_quotient_mk'.comp
    (continuous_subtype_val.comp (continuous_fst.comp (mixedSubgroupHomeomorph F h).continuous_invFun))

/-- Norm-one first-block matrices embed in the actual mixed subgroup. -/
theorem firstBlockEmbedding_mem_mixedSubgroup (u : normOneSubgroup F (m 0 + 1)) :
    firstBlockEmbedding h F u.val ∈ mixedSubgroup F h :=
  ⟨(u, 1), rfl⟩

/-- Equal determinant orders put the ratio in the norm-one subgroup. -/
theorem mul_inv_mem_normOne_of_ord_eq (u v : GeneralLinear (m 0 + 1) F)
    (huv : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant u : F) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant v : F)) :
    u * v⁻¹ ∈ normOneSubgroup F (m 0 + 1) := by
  rw [mem_normOneSubgroup_iff_normalizedAbs, ← Matrix.GeneralLinearGroup.val_det_apply,
    ← (⟨⟩ : LocalFieldData F).ord_eq_zero_iff_normalizedAbs]
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    (⟨⟩ : LocalFieldData F).ord_mul (GeneralLinear.determinant u).ne_zero
      (inv_ne_zero (GeneralLinear.determinant v).ne_zero),
    (⟨⟩ : LocalFieldData F).ord_inv, huv, add_neg_cancel]

/-- The quotient of the first coordinate ignores the first unipotent block. -/
theorem mixedFirstQuotient_block_mul (b : TwoBlockUnipotentQuotient.blockUnipotent h F)
    (u : normOneSubgroup F (m 0 + 1)) :
    mixedFirstQuotient F h
      ⟨b.val * firstBlockEmbedding h F u.val,
        mul_mem (blockUnipotent_le_mixedSubgroup F h b.property)
          (firstBlockEmbedding_mem_mixedSubgroup F h u)⟩ = Quotient.mk _ u.val := by
  obtain ⟨n, hn⟩ := b.property
  let n0 : normOneSubgroup F (m 0 + 1) :=
    ⟨(n 0).val, determinantNorm_eq_one_of_mem_upperUnipotent F
      (⟨⟩ : LocalFieldData F) (n 0).property⟩
  have he : b.val * firstBlockEmbedding h F u.val =
      mixedEmbedding F h (n0 * u, n 1) := by
    rw [← hn, TwoBlockUnipotentQuotient.blockEmbedding_apply,
      firstBlockEmbedding_apply, mixedEmbedding_apply, ← map_mul]
    apply congrArg ((succBlockShape m h).leviEmbedding F)
    funext i
    fin_cases i <;> simp [blockPair, n0]
  have hs : (⟨b.val * firstBlockEmbedding h F u.val,
      mul_mem (blockUnipotent_le_mixedSubgroup F h b.property)
        (firstBlockEmbedding_mem_mixedSubgroup F h u)⟩ : mixedSubgroup F h) =
      mixedSubgroupEquiv F h (n0 * u, n 1) := Subtype.ext he
  rw [hs]
  change Quotient.mk _ (((mixedSubgroupEquiv F h).symm
    (mixedSubgroupEquiv F h (n0 * u, n 1))).1.val) = _
  rw [MulEquiv.symm_apply_apply]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _ (n 0).property u.val

/-- Restricted first-block fibers have compact preimages of compact sets. -/
theorem fiberPoint_slice_isCompact_preimage (k : ℤ) (g : GeneralLinear (t + 1) F)
    {S : Set (TwoBlockUnipotentQuotient.BlockQuotient h F)} (hS : IsCompact S) :
    IsCompact (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k ∩
      (fun q => fiberPoint h F q g) ⁻¹' S) := by
  classical
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F
  let L := mixedSubgroup F h
  let := leftQuotient_t2Space H (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
  let B := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k ∩
    (fun q => fiberPoint h F q g) ⁻¹' S
  by_cases hB : B.Nonempty
  · obtain ⟨q0, hq0⟩ := hB
    induction q0 using Quotient.inductionOn with
    | h u0 =>
      obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H
        (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F) hS
      let D : Set L := Subtype.val ⁻¹'
        ((fun c => c * g⁻¹ * (firstBlockEmbedding h F u0)⁻¹) '' C)
      have hD : IsCompact D :=
        (isClosed_mixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
          (hC.image ((continuous_id.mul continuous_const).mul continuous_const))
      let ψ : L → LeftUnipotentQuotient (m 0) F :=
        fun l => rightTranslate _ u0 (mixedFirstQuotient F h l)
      have hψ : Continuous ψ :=
        (rightTranslate _ u0).continuous.comp (continuous_mixedFirstQuotient F h)
      have hf : Continuous (fun q => fiberPoint h F q g) :=
        (continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)
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
        have hxC : fiberPoint h F (Quotient.mk _ u) g ∈ leftQuotientMap H '' C := by
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
          mul_mem (blockUnipotent_le_mixedSubgroup F h hb)
            (firstBlockEmbedding_mem_mixedSubgroup F h v)⟩
        refine ⟨l, ⟨c, hc, he⟩, ?_⟩
        change rightTranslate _ u0 (mixedFirstQuotient F h l) = Quotient.mk _ u
        rw [mixedFirstQuotient_block_mul F h b v, rightTranslate_mk]
        simp [v, mul_assoc]
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    change IsCompact B
    rw [he]
    exact isCompact_empty

variable (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
  [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)

/-- Each fiber measure is finite on compact sets. -/
theorem fiberKernel_compact_ne_top (k : ℤ) (q : MixedQuotient F h)
    (S : Set (TwoBlockUnipotentQuotient.BlockQuotient h F)) (hS : IsCompact S) :
    fiberKernel F h νA hνA k q S ≠ ⊤ := by
  let := leftQuotient_t2Space (TwoBlockUnipotentQuotient.blockUnipotent h F)
    (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun q => fiberPoint h F q g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [fiberKernel_mk F h νA hνA k g, Measure.map_apply hf hS.measurableSet,
      Measure.restrict_apply (hf hS.measurableSet), Set.inter_comm]
    exact (fiberPoint_slice_isCompact_preimage F h k g hS).measure_ne_top

/-- Compact finiteness on the common countable compact cover proves kernel s-finiteness. -/
theorem fiberKernel_isSFinite (k : ℤ) : IsSFiniteKernel (fiberKernel F h νA hνA k) := by
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F
  let := leftQuotient_t2Space H (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (fiberKernel F h νA hνA k)
    (fiberKernel_compact_ne_top F h νA hνA k)

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
