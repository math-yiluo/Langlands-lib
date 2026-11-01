import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
import Langlands.Analysis.Local.QuotientKernelSupport
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The first-block slice fiber kernel

Construct the measurable kernel with the prescribed everywhere representative
formula, using right translation on the small quotient for descent.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

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
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  borel _
local instance : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

variable (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
  (hνA : NormOneRightInvariant F (m 0) νA)

omit [SFinite νA] in
include hνA in
/-- Right translation by a norm-one matrix preserves each restricted small measure. -/
theorem map_restrict_smallSlice (k : ℤ) (u : normOneSubgroup F (m 0 + 1)) :
    Measure.map (rightTranslate _ u.val)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) =
      νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k) := by
  have hS : rightTranslate _ u.val ⁻¹'
      RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k =
      RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k := by
    ext q
    rw [Set.mem_preimage,
      RankinSelberg.rightTranslate_mem_determinantSlice F.canonicalTopologicalData (m 0) k,
      ord_determinant_eq_zero F u.property, sub_zero]
  have hp := (hνA u).restrict_preimage_emb (rightTranslate _ u.val).measurableEmbedding
    (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)
  rw [hS] at hp
  exact hp.map_eq

/-- Joint continuity and s-finiteness of the small measure give measurable fiber measures. -/
theorem measurable_fiberMeasures (k : ℤ) :
    Measurable (fun g => Measure.map (fun q => fiberPoint h F.Carrier q g)
      (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k))) := by
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F.Carrier))
  let μ := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)
  have hf := (continuous_fiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [μ, Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

omit [SFinite νA] in
include hνA in
/-- Left multiplication from the mixed subgroup preserves the representative measures. -/
theorem fiberMeasures_mixedSubgroup_mul (k : ℤ) (l : mixedSubgroup F h)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Measure.map (fun q => fiberPoint h F.Carrier q (l.val * g))
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) =
      Measure.map (fun q => fiberPoint h F.Carrier q g)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) := by
  obtain ⟨⟨u, n⟩, hl⟩ := l.property
  have hf : Measurable (fun q => fiberPoint h F.Carrier q g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [fiberPoint_mixedEmbedding_mul F h]
  change Measure.map ((fun q => fiberPoint h F.Carrier q g) ∘ rightTranslate _ u.val) _ = _
  rw [← Measure.map_map hf (rightTranslate _ u.val).measurable,
    map_restrict_smallSlice F νA hνA k u]

/-- The actual descended slice kernel, with no extra scalar. -/
def fiberKernel (k : ℤ) :
    Kernel (MixedQuotient F h) (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := by
  let κ := descend (mixedSubgroup F h)
    (fun g => Measure.map (fun q => fiberPoint h F.Carrier q g)
      (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)))
    (fiberMeasures_mixedSubgroup_mul F h νA hνA k)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_mixedSubgroup F h) κ).2
    (measurable_fiberMeasures F h νA k)⟩

/-- The representative formula holds for every ambient group element. -/
theorem fiberKernel_mk (k : ℤ) (g : GeneralLinear (t + 1) F.Carrier) :
    fiberKernel F h νA hνA k (Quotient.mk _ g) =
      Measure.map (fun q => fiberPoint h F.Carrier q g)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) :=
  rfl

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
