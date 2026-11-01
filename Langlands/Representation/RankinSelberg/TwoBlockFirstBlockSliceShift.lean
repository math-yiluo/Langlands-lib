import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-!
# Determinant transport for the first-block quotient
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
open scoped NNReal ENNReal

universe uF

private def conjugation {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z : G) : G ≃ₜ* G :=
  { toMulEquiv := MulAut.conj z
    continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
    continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

private theorem conjugation_apply {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z x : G) :
    conjugation z x = z * x * z⁻¹ := rfl

private theorem measurePreserving_conjugation {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (z : G) :
    MeasurePreserving (conjugation z) μ μ :=
  (measurePreserving_mul_right μ z⁻¹).comp (measurePreserving_mul_left μ z)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sliceShiftTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance sliceShiftValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance sliceShiftLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance sliceShiftFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance sliceShiftFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance sliceShiftGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance sliceShiftGLBorel (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance sliceShiftGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance sliceShiftGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance sliceShiftNormOneMeasurable (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance sliceShiftNormOneBorel (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance sliceShiftNormOneSecondCountable (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance sliceShiftNormOneLocallyCompact (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance sliceShiftUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance sliceShiftUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance sliceShiftUnipotentSecondCountable (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance sliceShiftUnipotentLocallyCompact (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance sliceShiftSmallQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance sliceShiftSmallQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

private theorem conjugation_mem_normOne (n : ℕ) (z x : GeneralLinear n F.Carrier) :
    conjugation z x ∈ normOneSubgroup F n ↔ x ∈ normOneSubgroup F n := by
  change F.canonicalTopologicalData.determinantNorm n (z * x * z⁻¹) = 1 ↔
    F.canonicalTopologicalData.determinantNorm n x = 1
  simp [map_mul, map_inv]

private def normOneConjugation (n : ℕ) (z : GeneralLinear n F.Carrier) :
    normOneSubgroup F n ≃ₜ* normOneSubgroup F n :=
  subgroupAutomorphism _ (conjugation z) (conjugation_mem_normOne F n z)

/-- Ambient two-sided Haar invariance restricts exactly to the norm-one subgroup. -/
theorem map_normOneHaar_conjugation (n : ℕ) (z : GeneralLinear (n + 1) F.Carrier) :
    Measure.map (normOneConjugation F (n + 1) z) (normOneHaar F n) = normOneHaar F n := by
  let α := conjugation z
  let αA := normOneConjugation F (n + 1) z
  have hpre : α ⁻¹' (normOneSubgroup F (n + 1) : Set _) = normOneSubgroup F (n + 1) := by
    ext x
    exact conjugation_mem_normOne F (n + 1) z x
  have hp := (measurePreserving_conjugation (generalLinearHaar F.Carrier n) z).restrict_preimage_emb
      α.toHomeomorph.measurableEmbedding
      (normOneSubgroup F (n + 1) : Set _)
  rw [hpre] at hp
  apply (isOpenEmbedding_normOneSubtype F (n + 1)).measurableEmbedding.map_injective
  have hmα : Measurable α := α.continuous.measurable
  have hmαA : Measurable αA := αA.continuous.measurable
  have hmv : Measurable (Subtype.val :
      normOneSubgroup F (n + 1) → GeneralLinear (n + 1) F.Carrier) :=
    continuous_subtype_val.measurable
  change Measure.map Subtype.val (Measure.map αA (normOneHaar F n)) =
    Measure.map Subtype.val (normOneHaar F n)
  rw [Measure.map_map hmv hmαA]
  change Measure.map (α ∘ Subtype.val) (normOneHaar F n) = _
  rw [← Measure.map_map hmα hmv,
    map_normOneHaar F n, hp.map_eq]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance sliceShiftMixedMeasurable : MeasurableSpace (mixedSubgroup F h) := borel _
local instance sliceShiftMixedBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance sliceShiftMixedLocallyCompact : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance sliceShiftMixedQuotientMeasurable : MeasurableSpace (MixedQuotient F h) := borel _
local instance sliceShiftMixedQuotientBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance sliceShiftBlockQuotientMeasurable : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  borel _
local instance sliceShiftBlockQuotientBorel : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩

private theorem firstBlock_conjugation_mixedEmbedding (z : GeneralLinear (m 0 + 1) F.Carrier)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    conjugation (firstBlockEmbedding h F.Carrier z) (mixedEmbedding F h x) =
      mixedEmbedding F h (normOneConjugation F (m 0 + 1) z x.1, x.2) := by
  simp only [conjugation_apply, firstBlockEmbedding_apply, mixedEmbedding_apply,
    ← map_inv, ← map_mul]
  congr 2
  apply Prod.ext
  · rfl
  · simp

private theorem firstBlock_conjugation_mem_mixed (z : GeneralLinear (m 0 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    conjugation (firstBlockEmbedding h F.Carrier z) g ∈ mixedSubgroup F h ↔
      g ∈ mixedSubgroup F h := by
  constructor
  · rintro ⟨⟨u, n⟩, he⟩
    refine ⟨((normOneConjugation F (m 0 + 1) z).symm u, n), ?_⟩
    apply (conjugation (firstBlockEmbedding h F.Carrier z)).injective
    rw [firstBlock_conjugation_mixedEmbedding F h]
    simpa using he
  · rintro ⟨x, rfl⟩
    rw [firstBlock_conjugation_mixedEmbedding F h]
    exact mixedEmbedding_mem F h _

private def mixedConjugation (z : GeneralLinear (m 0 + 1) F.Carrier) :
    mixedSubgroup F h ≃ₜ* mixedSubgroup F h :=
  subgroupAutomorphism _ (conjugation (firstBlockEmbedding h F.Carrier z))
    (firstBlock_conjugation_mem_mixed F h z)

/-- The mixed product Haar is preserved by every first-block conjugation. -/
theorem map_mixedHaar_conjugation (z : GeneralLinear (m 0 + 1) F.Carrier) :
    Measure.map (mixedConjugation F h z) (mixedHaar F h) = mixedHaar F h := by
  let e := mixedSubgroupHomeomorph F h
  let α := mixedConjugation F h z
  let β := normOneConjugation F (m 0 + 1) z
  let μ := (normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1))
  have hme : Measurable e := e.continuous.measurable
  have hmα : Measurable α := α.continuous.measurable
  have hmβ : Measurable β := β.continuous.measurable
  have he : α ∘ e = e ∘ Prod.map β id := by
    funext x
    apply Subtype.ext
    exact firstBlock_conjugation_mixedEmbedding F h z x
  change Measure.map α (Measure.map e μ) = Measure.map e μ
  rw [Measure.map_map hmα hme, he,
    ← Measure.map_map hme (hmβ.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hmβ measurable_id,
    map_normOneHaar_conjugation F (m 0) z, Measure.map_id]

/-- Left multiplication by a first-block matrix on the actual mixed quotient. -/
def mixedLeftShift (z : GeneralLinear (m 0 + 1) F.Carrier) :
    MixedQuotient F h ≃ₜ MixedQuotient F h :=
  (quotientAutomorphism (mixedSubgroup F h)
    (conjugation (firstBlockEmbedding h F.Carrier z))
    (firstBlock_conjugation_mem_mixed F h z)).trans
      (rightTranslate _ (firstBlockEmbedding h F.Carrier z))

@[simp]
theorem mixedLeftShift_mk (z : GeneralLinear (m 0 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    mixedLeftShift F h z (Quotient.mk _ g) =
      Quotient.mk _ (firstBlockEmbedding h F.Carrier z * g) := by
  change (Quotient.mk _ (firstBlockEmbedding h F.Carrier z * g *
    (firstBlockEmbedding h F.Carrier z)⁻¹ * firstBlockEmbedding h F.Carrier z) :
      MixedQuotient F h) = _
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The restriction normalization makes this left shift measure preserving. -/
theorem measurePreserving_mixedLeftShift
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) νL)
    (z : GeneralLinear (m 0 + 1) F.Carrier) :
    MeasurePreserving (mixedLeftShift F h z) νL νL := by
  let α := conjugation (firstBlockEmbedding h F.Carrier z)
  let αL := mixedConjugation F h z
  have hdG : mulEquivHaarChar α = 1 := by
    have hp : Measure.map α (generalLinearHaar F.Carrier t) =
        generalLinearHaar F.Carrier t :=
      (measurePreserving_conjugation (generalLinearHaar F.Carrier t) _).map_eq
    rw [mulEquivHaarChar_eq (generalLinearHaar F.Carrier t) α]
    simp only [hp, Measure.haarScalarFactor_self]
  have hdL : mulEquivHaarChar αL = 1 := by
    rw [mulEquivHaarChar_eq (mixedHaar F h) αL]
    simp only [αL, map_mixedHaar_conjugation, Measure.haarScalarFactor_self]
  have hmap := hνL.map_quotientAutomorphism (mixedSubgroup F h)
    (isClosed_mixedSubgroup F h) α (firstBlock_conjugation_mem_mixed F h z)
  change Measure.map _ νL =
    (((mulEquivHaarChar αL / mulEquivHaarChar α : ℝ≥0) : ℝ≥0∞)) • νL at hmap
  rw [hdL, hdG, div_one, ENNReal.coe_one, one_smul] at hmap
  exact (hνL.right_invariant _).comp ⟨(quotientAutomorphism _ α _).measurable, hmap⟩

/-- Determinant order increases by exactly the first-block determinant order. -/
theorem determinantOrder_mixedLeftShift (z : GeneralLinear (m 0 + 1) F.Carrier)
    (q : MixedQuotient F h) :
    determinantOrder F h (mixedLeftShift F h z q) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) +
        determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mixedLeftShift_mk, determinantOrder_mk, determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul
        (GeneralLinear.determinant (firstBlockEmbedding h F.Carrier z)).ne_zero
        (GeneralLinear.determinant g).ne_zero,
      determinant_firstBlockEmbedding]

/-- The pushforward of the restricted zero outer slice has no extra factor. -/
theorem map_restrict_mixedLeftShift
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) νL)
    (z : GeneralLinear (m 0 + 1) F.Carrier) (k : ℤ)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k) :
    Measure.map (mixedLeftShift F h z) (νL.restrict (determinantSlice F h 0)) =
      νL.restrict (determinantSlice F h k) := by
  have hpre : mixedLeftShift F h z ⁻¹' determinantSlice F h k =
      determinantSlice F h 0 := by
    ext q
    simp only [Set.mem_preimage, mem_determinantSlice,
      determinantOrder_mixedLeftShift, hz, add_eq_left]
  have hp := (measurePreserving_mixedLeftShift F h νL hνL z).restrict_preimage_emb
    (mixedLeftShift F h z).measurableEmbedding (determinantSlice F h k)
  rw [hpre] at hp
  exact hp.map_eq

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
