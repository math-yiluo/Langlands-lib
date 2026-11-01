import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentMeasures

/-!
# Restriction-normalized measures for the first-block quotient

The Haar measure on the norm-one first block is pulled back from the ambient
general linear Haar measure through the open subgroup inclusion. The mixed
subgroup has the transported product Haar measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
local instance (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace

/-- The norm-one subgroup inclusion is an open embedding. -/
theorem isOpenEmbedding_normOneSubtype (n : ℕ) :
    Topology.IsOpenEmbedding (Subtype.val : normOneSubgroup F n → GeneralLinear n F.Carrier) :=
  (F.canonicalTopologicalData.isOpen_ker_determinantNorm n).isOpenEmbedding_subtypeVal

/-- Haar measure on `GL_(n+1)^0`, normalized by restriction from `GL_(n+1)`. -/
def normOneHaar (n : ℕ) : Measure (normOneSubgroup F (n + 1)) :=
  (generalLinearHaar F.Carrier n).comap Subtype.val

instance normOneHaar_isHaar (n : ℕ) : (normOneHaar F n).IsHaarMeasure :=
  Measure.IsHaarMeasure.comap (generalLinearHaar F.Carrier n)
    (f := (normOneSubgroup F (n + 1)).subtype) (mH := inferInstance)
    (isOpenEmbedding_normOneSubtype F (n + 1))

instance normOneHaar_regular (n : ℕ) : (normOneHaar F n).Regular :=
  Measure.Regular.comap' (generalLinearHaar F.Carrier n)
    (isOpenEmbedding_normOneSubtype F (n + 1))

instance normOneHaar_isMulRightInvariant (n : ℕ) :
    (normOneHaar F n).IsMulRightInvariant :=
  Measure.IsMulRightInvariant.comap (generalLinearHaar F.Carrier n)
    (f := (normOneSubgroup F (n + 1)).subtype)
    (isOpenEmbedding_normOneSubtype F (n + 1)).measurableEmbedding

/-- The normalization is an exact equality of measures. -/
theorem map_normOneHaar (n : ℕ) :
    Measure.map Subtype.val (normOneHaar F n) =
      (generalLinearHaar F.Carrier n).restrict (normOneSubgroup F (n + 1)) := by
  have he : Set.range (Subtype.val : normOneSubgroup F (n + 1) →
      GeneralLinear (n + 1) F.Carrier) = (normOneSubgroup F (n + 1) : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact ((isOpenEmbedding_normOneSubtype F (n + 1)).measurableEmbedding.map_comap
    (generalLinearHaar F.Carrier n)).trans (congrArg _ he)

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : MeasurableSpace (mixedSubgroup F h) := borel _
local instance : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance : SecondCountableTopology (normOneSubgroup F (m 0 + 1)) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance : LocallyCompactSpace (normOneSubgroup F (m 0 + 1)) :=
  (isOpenEmbedding_normOneSubtype F (m 0 + 1)).locallyCompactSpace

/-- Product Haar measure on the actual mixed subgroup. -/
def mixedHaar : Measure (mixedSubgroup F h) :=
  Measure.map (mixedSubgroupEquiv F h)
    ((normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1)))

instance mixedHaar_isHaar : (mixedHaar F h).IsHaarMeasure := by
  exact (mixedSubgroupHomeomorph F h).isHaarMeasure_map
    ((normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1)))

instance mixedHaar_regular : (mixedHaar F h).Regular := by
  let K : TopologicalSpace.PositiveCompacts
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :=
    Classical.arbitrary _
  have : ((normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1))).Regular :=
    Measure.regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_ne_top
  exact Measure.Regular.map (mixedSubgroupHomeomorph F h).toHomeomorph

instance mixedHaar_isMulRightInvariant : (mixedHaar F h).IsMulRightInvariant := by
  let e := mixedSubgroupHomeomorph F h
  let μ := (normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1))
  have hemeas : Measurable
      (e : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier →
        mixedSubgroup F h) := e.continuous.measurable
  change (Measure.map e μ).IsMulRightInvariant
  refine ⟨fun g => ?_⟩
  rw [Measure.map_map (measurable_mul_const g) hemeas]
  have he : (fun x => e x * g) = e ∘ (fun x => x * e.symm g) := by
    funext x
    simp
  change Measure.map (fun x => e x * g) μ = Measure.map e μ
  rw [he, ← Measure.map_map hemeas (measurable_mul_const _), map_mul_right_eq_self]

/-- Compatible quotient existence for the fixed restriction-normalized pair. -/
theorem mixed_compatibleMeasureExists
    [MeasurableSpace (MixedQuotient F h)] [BorelSpace (MixedQuotient F h)] :
    CompatibleMeasureExists (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) :=
  Langlands.QuotientIntegration.compatibleMeasureExists (mixedSubgroup F h)
    (isClosed_mixedSubgroup F h) (generalLinearHaar F.Carrier t) (mixedHaar F h)

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
