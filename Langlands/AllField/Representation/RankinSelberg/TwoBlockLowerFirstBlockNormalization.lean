import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasures
/-!
# Integral normalization of the lower mixed Haar

The actual lower mixed integral subgroup has normalized mass one. The product
formed from any supplied rectangular Haar has mass equal to its integral cube.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedHaar lowerMixedHaar_integral lowerMixedHaar_isHaar lowerMixedHaar_isMulRightInvariant lowerMixedHaar_regular lowerMixedIntegralOpen lowerMixedIntegralOpen_isCompact lowerMixedProductMeasure lowerMixedProductMeasure_eq_smul lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_compatibleMeasureExists lowerMixed_decomposition lowerMixed_preimage_integral lowerNormalizationInstance01 lowerNormalizationInstance02 lowerNormalizationInstance03 lowerNormalizationInstance04 lowerNormalizationInstance05 lowerNormalizationInstance06 lowerNormalizationInstance07 lowerNormalizationInstance08 lowerNormalizationInstance10 lowerNormalizationInstance11 lowerNormalizationInstance12 lowerNormalizationInstance13 lowerNormalizationInstance14 lowerNormalizationInstance15 lowerNormalizationInstance16 lowerNormalizationInstance17 lowerNormalizationInstance18 lowerNormalizationInstance19 lowerNormalizationInstance20 lowerNormalizationInstance21 lowerNormalizationInstance22 lowerNormalizationInstance23 lowerNormalizationInstance24 lowerNormalizationInstance25 lowerNormalizationInstance26 lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice normOneHaar_integral projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory TopologicalSpace
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul iUnion_determinantSlice integerCube_mass_pos_lt_top isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_mk radicalAverage_rightTranslate
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice radicalAverage radicalAverage_mk
open Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration
open scoped ENNReal

universe uF uK

section Algebra


end Algebra

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerNormalizationInstance04 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerNormalizationInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerNormalizationInstance06 : MeasurableSpace F := borel _
local instance lowerNormalizationInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerNormalizationInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerNormalizationInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerNormalizationInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerNormalizationInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerNormalizationInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerNormalizationInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerNormalizationInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerNormalizationInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerNormalizationInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerNormalizationInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerNormalizationInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerNormalizationInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerNormalizationInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerNormalizationInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerNormalizationInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerNormalizationInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F
local notation "O" => Valuation.integer (ValuativeRel.valuation F)

/-- Actual integral points in the lower mixed subgroup, as a compact open subgroup. -/
def lowerMixedIntegralOpen : OpenSubgroup (lowerMixedSubgroup F h) :=
  OpenSubgroup.comap (lowerMixedSubgroup F h).subtype continuous_subtype_val
    (Conductor.levelOpenSubgroup F t 0)

theorem lowerMixedIntegralOpen_isCompact :
    IsCompact (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) :=
  (isClosed_lowerMixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
    (Conductor.isCompact_levelOpenSubgroup F t 0)

/-- Haar measure chosen before any rectangular measure and normalized on the
actual integral points. -/
def lowerMixedHaar : Measure (lowerMixedSubgroup F h) :=
  normalizedCompactOpenHaar (lowerMixedIntegralOpen F h) (lowerMixedIntegralOpen_isCompact F h)

instance lowerMixedHaar_isHaar : (lowerMixedHaar F h).IsHaarMeasure := by
  unfold lowerMixedHaar
  infer_instance

instance lowerMixedHaar_regular : (lowerMixedHaar F h).Regular := by
  unfold lowerMixedHaar
  infer_instance

@[simp] theorem lowerMixedHaar_integral :
    lowerMixedHaar F h (Subtype.val ⁻¹'
      (Conductor.integralSubgroup O t : Set (GeneralLinear (t + 1) F))) = 1 := by
  have he : Subtype.val ⁻¹' (Conductor.integralSubgroup O t : Set _) =
      (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) := by
    ext x
    change x.val ∈ Conductor.integralSubgroup O t ↔
      x.val ∈ Conductor.levelSubgroup F t 0
    rw [Conductor.levelSubgroup_zero]
  rw [he]
  exact normalizedCompactOpenHaar_self _ _

private theorem integralSubgroup_le_normOne (n : ℕ) :
    Conductor.integralSubgroup O n ≤ normOneSubgroup F (n + 1) := by
  intro g hg
  rw [mem_normOneSubgroup_iff]
  let T := (⟨⟩ : LocalFieldData F)
  obtain ⟨hge, hgi⟩ := (Conductor.mem_integralSubgroup O n g).mp hg
  have hdet : ∀ a : GeneralLinear (n + 1) F, (∀ i j, a i j ∈ T.Integers) →
      (GeneralLinear.determinant a : F) ∈ T.Integers := by
    intro a ha
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) T.Integers := fun i j => ⟨a i j, ha i j⟩
    have he : T.Integers.subtype.mapMatrix A = a.val := by ext i j; rfl
    have hd : (GeneralLinear.determinant a : F) = T.Integers.subtype A.det := by
      rw [RingHom.map_det, he, Matrix.GeneralLinearGroup.val_det_apply]
    rw [hd]
    exact A.det.property
  have h1 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g hge)
  have h2 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g⁻¹ hgi)
  have hp : T.normalizedAbs (GeneralLinear.determinant g : F) *
      T.normalizedAbs (GeneralLinear.determinant g⁻¹ : F) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hn := T.normalizedAbs_nonneg (GeneralLinear.determinant g : F)
  have hni := T.normalizedAbs_nonneg (GeneralLinear.determinant g⁻¹ : F)
  have hv : T.normalizedAbs (GeneralLinear.determinant g : F) = 1 := by nlinarith
  apply Units.ext
  apply NNReal.eq
  rw [T.determinantNorm_coe]
  simpa using hv

/-- The restriction-normalized norm-one Haar gives its integral subgroup mass one. -/
theorem normOneHaar_integral (n : ℕ) :
    normOneHaar F n (Subtype.val ⁻¹'
      (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F))) = 1 := by
  have hK : MeasurableSet (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F)) :=
    (Conductor.isOpen_integralSubgroup O n (⟨⟩ : LocalFieldData F).isOpen_integers).measurableSet
  have he := congrArg (fun μ : Measure (GeneralLinear (n + 1) F) =>
      μ (Conductor.integralSubgroup O n : Set _)) (map_normOneHaar F n)
  rw [Measure.map_apply (isOpenEmbedding_normOneSubtype F (n + 1)).continuous.measurable hK,
    Measure.restrict_apply hK] at he
  have hs : (Conductor.integralSubgroup O n : Set (GeneralLinear (n + 1) F)) ∩
      (normOneSubgroup F (n + 1) : Set _) = Conductor.integralSubgroup O n :=
    Set.inter_eq_left.mpr (integralSubgroup_le_normOne F n)
  rwa [hs, generalLinearHaar_integralSubgroup] at he

/-- Integral points in the actual coordinates form the three expected integral sets. -/
theorem lowerMixed_preimage_integral :
    lowerMixedSubgroupHomeomorph F h ⁻¹'
      (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) =
      {Z : R | ∀ i j, Z i j ∈ O} ×ˢ
        ((Subtype.val ⁻¹' (Conductor.integralSubgroup O (m 0) : Set _)) ×ˢ
          (unipotentIntegralOpen F (m 1) : Set _)) := by
  ext ⟨Z, a, n⟩
  change lowerProduct h F Z a.val n.val ∈ Conductor.levelSubgroup F t 0 ↔ _
  rw [Conductor.levelSubgroup_zero, lowerProduct_mem_integralSubgroup_iff]
  change _ ↔ (∀ i j, Z i j ∈ O) ∧ a.val ∈ Conductor.integralSubgroup O (m 0) ∧
    n.val ∈ Conductor.levelSubgroup F (m 1) 0
  rw [Conductor.levelSubgroup_zero]

/-- The coefficient of the coordinate product is the supplied integral-cube mass. -/
theorem lowerMixedProductMeasure_eq_smul
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    lowerMixedProductMeasure F h μR = μR {Z | ∀ i j, Z i j ∈ O} • lowerMixedHaar F h := by
  have key := Measure.isMulLeftInvariant_eq_smul
    (lowerMixedProductMeasure F h μR) (lowerMixedHaar F h)
  have hc := DFunLike.congr_fun key (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h))
  have hK : MeasurableSet (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) :=
    (lowerMixedIntegralOpen F h).isOpen.measurableSet
  have h1 : lowerMixedHaar F h (lowerMixedIntegralOpen F h : Set (lowerMixedSubgroup F h)) = 1 :=
    normalizedCompactOpenHaar_self _ _
  change Measure.map (lowerMixedSubgroupHomeomorph F h)
    (μR.prod ((normOneHaar F (m 0)).prod (unipotentHaar F (m 1)))) _ = _ at hc
  rw [Measure.map_apply (lowerMixedSubgroupHomeomorph F h).continuous.measurable hK,
    lowerMixed_preimage_integral, Measure.prod_prod, Measure.prod_prod,
    normOneHaar_integral, unipotentHaar_integral, one_mul, mul_one,
    Measure.coe_nnreal_smul_apply, h1, mul_one] at hc
  rw [hc, Measure.coe_nnreal_smul]
  exact key

instance lowerMixedHaar_isMulRightInvariant : (lowerMixedHaar F h).IsMulRightInvariant := by
  have key := Measure.isMulLeftInvariant_eq_smul (lowerMixedHaar F h)
    (lowerMixedProductMeasure F h (Measure.addHaar : Measure R))
  rw [key]
  infer_instance

/-- Compatible quotient existence for the one normalized lower mixed Haar. -/
theorem lowerMixed_compatibleMeasureExists
    [MeasurableSpace (LowerMixedQuotient F h)] [BorelSpace (LowerMixedQuotient F h)] :
    CompatibleMeasureExists (lowerMixedSubgroup F h)
      (generalLinearHaar F t) (lowerMixedHaar F h) :=
  Langlands.QuotientIntegration.compatibleMeasureExists (lowerMixedSubgroup F h)
    (isClosed_lowerMixedSubgroup F h) (generalLinearHaar F t) (lowerMixedHaar F h)

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
