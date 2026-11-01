import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measure in the actual lower mixed coordinates

The coordinate product measure is invariant on both sides, although its
coordinate homeomorphism is not a group homomorphism.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration TopologicalSpace
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
open scoped ENNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasuresInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerMeasuresInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerMeasuresInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerMeasuresInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerMeasuresInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerMeasuresInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerMeasuresInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerMeasuresInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerMeasuresInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerMeasuresInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerMeasuresInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerMeasuresInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerMeasuresInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerMeasuresInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerMeasuresInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerMeasuresInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerMeasuresInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasuresInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerMeasuresInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerMeasuresInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerMeasuresInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasuresInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerMeasuresInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerMeasuresInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerMeasuresInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasuresInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F.Carrier (m 1))

/-- Product of the supplied rectangular Haar and the fixed diagonal measures,
transported by the actual lower mixed coordinate homeomorphism. -/
def lowerMixedProductMeasure (μR : Measure R) : Measure (lowerMixedSubgroup F h) :=
  Measure.map (lowerMixedSubgroupHomeomorph F h) (μR.prod μD)

private theorem measurePreserving_coordinateLeft (μR : Measure R) [μR.IsAddHaarMeasure]
    (x : R × D) :
    MeasurePreserving
      (fun y : R × D =>
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2))
      (μR.prod μD) (μR.prod μD) := by
  have hc := measurePreserving_radicalChange F μR 0 x.2.1⁻¹ x.2.2⁻¹
  have hl : MeasurePreserving
      (fun Z : R => x.1 + x.2.2.val.val * Z * (x.2.1.val⁻¹).val) μR μR := by
    simpa only [Function.comp_def, radicalChange_apply, Subgroup.coe_inv, inv_inv,
      add_zero] using (measurePreserving_add_left μR x.1).comp hc
  exact hl.prod (measurePreserving_mul_left μD x.2)

private theorem measurePreserving_coordinateRight (μR : Measure R) [μR.IsAddHaarMeasure]
    (x : R × D) :
    MeasurePreserving
      (fun y : R × D =>
        (y.1 + y.2.2.val.val * x.1 * (y.2.1.val⁻¹).val, y.2 * x.2))
      (μR.prod μD) (μR.prod μD) := by
  have hc : Continuous (fun y : D × R =>
      y.2 + y.1.2.val.val * x.1 * (y.1.1.val⁻¹).val) := by
    exact continuous_snd.add
      (((Units.continuous_val.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_fst))).matrix_mul continuous_const).matrix_mul
          (Units.continuous_val.comp (continuous_subtype_val.comp
            (continuous_fst.comp continuous_fst)).inv))
  have hp := (measurePreserving_mul_right μD x.2).skew_product hc.measurable
    (Filter.Eventually.of_forall (fun d : D => map_add_right_eq_self μR
      (d.2.val.val * x.1 * (d.1.val⁻¹).val)))
  exact (Measure.measurePreserving_swap (μ := μD) (ν := μR)).comp
    (hp.comp (Measure.measurePreserving_swap (μ := μR) (ν := μD)))

instance lowerMixedProductMeasure_isMulLeftInvariant
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsMulLeftInvariant := by
  let e := lowerMixedSubgroupHomeomorph F h
  refine ⟨fun g => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective g
  change Measure.map (fun z => e x * z) (Measure.map e (μR.prod μD)) =
    Measure.map e (μR.prod μD)
  rw [Measure.map_map (measurable_const_mul (e x)) e.continuous.measurable]
  have he : (fun y => e x * e y) = e ∘
      (fun y : R × D =>
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2)) := by
    funext y
    exact lowerMixedSubgroupEquiv_mul F h x y
  change Measure.map (fun y => e x * e y) (μR.prod μD) = _
  rw [he, ← Measure.map_map e.continuous.measurable
    (measurePreserving_coordinateLeft F μR x).measurable,
    (measurePreserving_coordinateLeft F μR x).map_eq]

instance lowerMixedProductMeasure_isMulRightInvariant
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsMulRightInvariant := by
  let e := lowerMixedSubgroupHomeomorph F h
  refine ⟨fun g => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective g
  change Measure.map (fun z => z * e x) (Measure.map e (μR.prod μD)) =
    Measure.map e (μR.prod μD)
  rw [Measure.map_map (measurable_mul_const (e x)) e.continuous.measurable]
  have he : (fun y => e y * e x) = e ∘
      (fun y : R × D =>
        (y.1 + y.2.2.val.val * x.1 * (y.2.1.val⁻¹).val, y.2 * x.2)) := by
    funext y
    exact lowerMixedSubgroupEquiv_mul F h y x
  change Measure.map (fun y => e y * e x) (μR.prod μD) = _
  rw [he, ← Measure.map_map e.continuous.measurable
    (measurePreserving_coordinateRight F μR x).measurable,
    (measurePreserving_coordinateRight F μR x).map_eq]

instance lowerMixedProductMeasure_isHaar
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts :=
    Measure.IsFiniteMeasureOnCompacts.map (μR.prod μD) (lowerMixedSubgroupHomeomorph F h)
  toIsOpenPosMeasure := (lowerMixedSubgroupHomeomorph F h).continuous.isOpenPosMeasure_map
    (lowerMixedSubgroupHomeomorph F h).surjective

instance lowerMixedProductMeasure_regular
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).Regular := by
  let K : PositiveCompacts (lowerMixedSubgroup F h) := Classical.arbitrary _
  exact Measure.regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
    K.isCompact.measure_ne_top

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
