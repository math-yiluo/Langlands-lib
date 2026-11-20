import Langlands.Global.LeftCosetHaarMeasure
import Langlands.Global.LeftCosetFundamentalDomain

/-! # Integrable majorants on `Γ \ H` from images of compact sets

For a discrete subgroup `Γ` of a second-countable Hausdorff topological group `H`, a family of
compact sets `B i ⊆ H` of uniformly bounded measure and a summable family of reals `β i`, the
function `x ↦ ∑ᵢ β i · 1_{Γ B i}(x)` on `Γ \ H` (computed in `ℝ≥0∞` and converted to `ℝ`) is
integrable for the discrete quotient measure, and it dominates `β i` on the image of `B i`. -/

noncomputable section

universe u v

open MeasureTheory Set Topology
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H)

variable [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H]

/-- The image of a compact set in `Γ \ H` is measurable, for a countable subgroup `Γ`. -/
theorem measurableSet_mk_image [Countable Γ] {B : Set H} (hB : IsCompact B) :
    MeasurableSet (mk Γ '' B) := by
  change MeasurableSet (Quotient.mk'' ⁻¹' (mk Γ '' B))
  rw [show (Quotient.mk'' : H → LeftCosetSpace Γ) = mk Γ from rfl, preimage_image_mk]
  refine MeasurableSet.iUnion fun γ => ?_
  have hc : IsCompact (γ • B) := by
    rw [← Set.image_smul]
    exact hB.image (continuous_const.mul continuous_id)
  exact hc.isClosed.measurableSet

omit [T2Space H] in
/-- The quotient measure of the image of a set is at most the measure of the set. -/
theorem quotientMeasure_mk_image_le [Countable Γ] (ν : Measure H) [SMulInvariantMeasure Γ H ν]
    {s : Set H} (hs : IsFundamentalDomain Γ s ν) {B : Set H}
    (hB : MeasurableSet (mk Γ '' B)) :
    quotientMeasure Γ ν s (mk Γ '' B) ≤ ν B := by
  rw [quotientMeasure_apply Γ ν s hB, preimage_image_mk, iUnion_inter, hs.measure_eq_tsum B]
  exact measure_iUnion_le _

/-- The nonnegative real sum `∑ᵢ (β i)⁺ · 1_{Γ B i}` used as an integrable majorant. -/
def imageIndicatorSum {ι : Type v} (B : ι → Set H) (β : ι → ℝ) (x : LeftCosetSpace Γ) : ℝ :=
  (∑' i, (mk Γ '' B i).indicator (fun _ => ENNReal.ofReal (β i)) x).toReal

omit [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H] in
theorem tsum_ofReal_ne_top {ι : Type v} {β : ι → ℝ} (hβ : Summable β) :
    ∑' i, ENNReal.ofReal (β i) ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' i, |β i|)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg (β i)) hβ.abs]
  exact ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (le_abs_self _)

omit [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H] in
/-- On the image of `B i` the majorant is at least `β i`. -/
theorem le_imageIndicatorSum {ι : Type v} (B : ι → Set H) {β : ι → ℝ} (hβ : Summable β)
    {i : ι} {x : LeftCosetSpace Γ} (hx : x ∈ mk Γ '' B i) :
    β i ≤ imageIndicatorSum Γ B β x := by
  have hle : ENNReal.ofReal (β i) ≤
      ∑' j, (mk Γ '' B j).indicator (fun _ => ENNReal.ofReal (β j)) x := by
    refine le_trans ?_ (ENNReal.le_tsum i)
    rw [Set.indicator_of_mem hx]
  have hfin : ∑' j, (mk Γ '' B j).indicator (fun _ => ENNReal.ofReal (β j)) x ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_ofReal_ne_top hβ)
      (ENNReal.tsum_le_tsum fun j => Set.indicator_le_self _ _ x)
  calc β i ≤ (ENNReal.ofReal (β i)).toReal := by
        rw [ENNReal.toReal_ofReal']
        exact le_max_left _ _
    _ ≤ imageIndicatorSum Γ B β x := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hle

variable [SecondCountableTopology H]

/-- The majorant is integrable for the discrete quotient measure when the sets `B i` are compact
of measure at most a finite constant and `β` is summable. -/
theorem integrable_imageIndicatorSum (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] {ι : Type v} [Countable ι] (B : ι → Set H)
    (hB : ∀ i, IsCompact (B i)) {m : ℝ≥0∞} (hm : m ≠ ∞) (hνB : ∀ i, ν (B i) ≤ m)
    {β : ι → ℝ} (hβ : Summable β) :
    Integrable (imageIndicatorSum Γ B β) (discreteQuotientMeasure Γ hΓ ν) := by
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  have hS : ∀ i, MeasurableSet (mk Γ '' B i) := fun i => measurableSet_mk_image Γ (hB i)
  have hmeas : Measurable fun x : LeftCosetSpace Γ =>
      ∑' i, (mk Γ '' B i).indicator (fun _ => ENNReal.ofReal (β i)) x :=
    Measurable.tsum fun i => measurable_const.indicator (hS i)
  refine integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable ?_
  rw [lintegral_tsum fun i => (measurable_const.indicator (hS i)).aemeasurable]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (tsum_ofReal_ne_top hβ) hm) ?_
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [lintegral_indicator_const (hS i)]
  gcongr
  exact (quotientMeasure_mk_image_le Γ ν (isFundamentalDomain Γ hΓ ν) (hS i)).trans (hνB i)

omit [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] in
theorem mk_out (x : LeftCosetSpace Γ) : mk Γ (Quotient.out x) = x :=
  Quotient.out_eq x

/-- **Integrable majorant from a compact cover.** Let `Ω ⊆ H` be compact of finite measure for
a left-invariant measure `ν`, let `Γ` be a subgroup and `Γw` a discrete subgroup of `H`, and let
`cls : Γ → E` be a map to a countable type whose fibres lie in single right cosets of `Γw`
(`cls δ = cls δ'` implies `δ' δ⁻¹ ∈ Γw`). Then for every summable `β : E → ℝ` there is an
integrable function `b` on `Γw \ H` with `β (cls δ) ≤ b (Γw δ ω)` for all `δ ∈ Γ`, `ω ∈ Ω`. -/
theorem exists_integrable_majorant_of_cover (Γw : Subgroup H)
    (hΓw : IsDiscrete (Γw : Set H)) (ν : Measure H) [ν.IsMulLeftInvariant] {Ω : Set H}
    (hΩ : IsCompact Ω) (hΩν : ν Ω ≠ ∞) {E : Type v} [Countable E] (cls : Γ → E)
    (hcls : ∀ δ δ' : Γ, cls δ = cls δ' → (δ' : H) * (δ : H)⁻¹ ∈ Γw) {β : E → ℝ}
    (hβ : Summable β) :
    ∃ b : LeftCosetSpace Γw → ℝ, Integrable b (discreteQuotientMeasure Γw hΓw ν) ∧
      ∀ (δ : Γ) (ω : H), ω ∈ Ω → β (cls δ) ≤ b (mk Γw ((δ : H) * ω)) := by
  classical
  let rep : E → H := fun i => if h : ∃ δ : Γ, cls δ = i then ((Classical.choose h : Γ) : H) else 1
  let B : E → Set H := fun i => if ∃ δ : Γ, cls δ = i then rep i • Ω else ∅
  have hB : ∀ i, IsCompact (B i) := by
    intro i
    by_cases h : ∃ δ : Γ, cls δ = i
    · simp only [B, h, ↓reduceIte]
      exact hΩ.smul (rep i)
    · simp only [B, h, ↓reduceIte]
      exact isCompact_empty
  have hνB : ∀ i, ν (B i) ≤ ν Ω := by
    intro i
    by_cases h : ∃ δ : Γ, cls δ = i
    · simp only [B, h, ↓reduceIte]
      rw [measure_smul]
    · simp only [B, h, ↓reduceIte, measure_empty]
      exact zero_le
  refine ⟨imageIndicatorSum Γw B β,
    integrable_imageIndicatorSum Γw hΓw ν B hB hΩν hνB hβ, ?_⟩
  intro δ ω hω
  have h : ∃ δ' : Γ, cls δ' = cls δ := ⟨δ, rfl⟩
  have hrep : rep (cls δ) = ((Classical.choose h : Γ) : H) := by simp only [rep, h, ↓reduceDIte]
  have hmem : (δ : H) * ((Classical.choose h : Γ) : H)⁻¹ ∈ Γw :=
    hcls _ δ (Classical.choose_spec h)
  refine le_imageIndicatorSum Γw B hβ ⟨rep (cls δ) * ω, ?_, ?_⟩
  · simp only [B, h, ↓reduceIte]
    exact Set.smul_mem_smul_set hω
  · rw [mk_eq_mk_iff, hrep]
    simpa [mul_assoc] using hmem

end Langlands.Global.LeftCosetSpace
