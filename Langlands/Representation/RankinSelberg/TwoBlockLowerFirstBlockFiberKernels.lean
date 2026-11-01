import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel

/-!
# Actual lower mixed quotient fiber kernels

Measurable descent of the rectangular and small-slice pushforward measures.
These constructions supply neither a normalized measure tower nor convergence.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

section Radical

variable (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))

/-- Joint continuity makes the unnormalized rectangular pushforwards measurable. -/
theorem measurable_radicalFiberMeasures [SFinite μR] :
    Measurable (fun g => Measure.map (fun Z => radicalFiberPoint F h Z g) μR) := by
  have hf := (continuous_radicalFiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μR))
  simpa only [Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

/-- The supplied Haar measure is preserved by the actual change of representative. -/
theorem radicalFiberMeasures_lowerMixed_mul [μR.IsAddHaarMeasure]
    (l : lowerMixedSubgroup F h) (g : GeneralLinear (t + 1) F.Carrier) :
    Measure.map (fun Z => radicalFiberPoint F h Z (l.val * g)) μR =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  have hf : Measurable (fun Z => radicalFiberPoint F h Z g) :=
    ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [radicalFiberPoint_lowerRadical_mixedEmbedding_mul F h]
  change Measure.map ((fun Z => radicalFiberPoint F h Z g) ∘ radicalChange F Z0 a0 n) μR = _
  rw [← Measure.map_map hf (measurePreserving_radicalChange F μR Z0 a0 n).measurable,
    (measurePreserving_radicalChange F μR Z0 a0 n).map_eq]

/-- The actual rectangular kernel, with the supplied measure retained without rescaling. -/
def radicalKernel [μR.IsAddHaarMeasure] :
    Kernel (LowerMixedQuotient F h) (MixedQuotient F h) := by
  let κ := descend (lowerMixedSubgroup F h)
    (fun g => Measure.map (fun Z => radicalFiberPoint F h Z g) μR)
    (radicalFiberMeasures_lowerMixed_mul F h μR)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_lowerMixedSubgroup F h) κ).2
    (measurable_radicalFiberMeasures F h μR)⟩

/-- The rectangular representative law holds everywhere. -/
theorem radicalKernel_mk [μR.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F.Carrier) :
    radicalKernel F h μR (Quotient.mk _ g) =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR := rfl

end Radical

section FirstBlock

variable (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
  (hνA : NormOneRightInvariant F (m 0) νA)

/-- Joint continuity makes the small-slice pushforwards measurable. -/
theorem measurable_firstBlockFiberMeasures (k : ℤ) :
    Measurable (fun g => Measure.map (fun q => firstBlockFiberPoint F h q g)
      (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k))) := by
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F.Carrier))
  let μ := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)
  have hf := (continuous_firstBlockFiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [μ, Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

omit [SFinite νA] in
include hνA in
/-- Norm-one right invariance on the small quotient gives lower mixed descent. -/
theorem firstBlockFiberMeasures_lowerMixed_mul (k : ℤ) (l : lowerMixedSubgroup F h)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Measure.map (fun q => firstBlockFiberPoint F h q (l.val * g))
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) =
      Measure.map (fun q => firstBlockFiberPoint F h q g)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  have hf : Measurable (fun q => firstBlockFiberPoint F h q g) :=
    ((continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul F h]
  change Measure.map ((fun q => firstBlockFiberPoint F h q g) ∘ rightTranslate _ a0.val) _ = _
  rw [← Measure.map_map hf (rightTranslate _ a0.val).measurable,
    TwoBlockFirstBlockQuotient.map_restrict_smallSlice F νA hνA k a0]

/-- The actual unweighted first-block slice kernel. -/
def firstBlockKernel (k : ℤ) :
    Kernel (LowerMixedQuotient F h) (LowerQuotient h F.Carrier) := by
  let κ := descend (lowerMixedSubgroup F h)
    (fun g => Measure.map (fun q => firstBlockFiberPoint F h q g)
      (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)))
    (firstBlockFiberMeasures_lowerMixed_mul F h νA hνA k)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_lowerMixedSubgroup F h) κ).2
    (measurable_firstBlockFiberMeasures F h νA k)⟩

/-- The first-block representative law holds for every ambient representative. -/
theorem firstBlockKernel_mk (k : ℤ) (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockKernel F h νA hνA k (Quotient.mk _ g) =
      Measure.map (fun q => firstBlockFiberPoint F h q g)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) := rfl

end FirstBlock

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
