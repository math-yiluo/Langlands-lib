import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Basic

/-! # Families with locally uniformly convergent sums of norms -/

noncomputable section
open Filter Topology
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

variable {ι κ X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A family of functions whose sums of norms converge pointwise, and uniformly on every compact
set. -/
def LocUnifSummable (f : ι → X → ℂ) : Prop :=
  (∀ x, Summable fun i => ‖f i x‖) ∧
    ∀ C : Set X, IsCompact C →
      TendstoUniformlyOn (fun (s : Finset ι) x => ∑ i ∈ s, ‖f i x‖)
        (fun x => ∑' i, ‖f i x‖) atTop C

/-- The tail of a summable family of nonnegative reals outside a finite set. -/
theorem tsum_norm_sub_sum {f : ι → ℂ} (hf : Summable fun i => ‖f i‖) (s : Finset ι) :
    ∑' i, ‖f i‖ - ∑ i ∈ s, ‖f i‖ = ∑' i : {i // i ∉ s}, ‖f i‖ := by
  rw [← hf.sum_add_tsum_subtype_compl s]
  simp

theorem norm_tsum_sub_sum_le {f : ι → ℂ} (hf : Summable fun i => ‖f i‖) (s : Finset ι) :
    ‖∑' i, f i - ∑ i ∈ s, f i‖ ≤ ∑' i, ‖f i‖ - ∑ i ∈ s, ‖f i‖ := by
  have hfs : Summable f := hf.of_norm
  rw [← hfs.sum_add_tsum_subtype_compl s, add_sub_cancel_left, tsum_norm_sub_sum hf]
  exact norm_tsum_le_tsum_norm (hf.subtype _)

/-- Locally uniform summability of norms gives locally uniform convergence of the sums. -/
theorem LocUnifSummable.tendstoUniformlyOn {f : ι → X → ℂ} (hf : LocUnifSummable f)
    {C : Set X} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (s : Finset ι) x => ∑ i ∈ s, f i x) (fun x => ∑' i, f i x) atTop C := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.mp (hf.2 C hC)) ε hε
  filter_upwards [h] with s hs x hx
  have h1 := hs x hx
  rw [Real.dist_eq, abs_lt] at h1
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_tsum_sub_sum_le (hf.1 x) s) ?_
  linarith

/-- The sum of a locally uniformly summable family of continuous functions is continuous. -/
theorem LocUnifSummable.continuous_tsum [WeaklyLocallyCompactSpace X] {f : ι → X → ℂ}
    (hf : LocUnifSummable f) (hc : ∀ i, Continuous (f i)) :
    Continuous fun x => ∑' i, f i x := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  have hcont : ContinuousOn (fun x => ∑' i, f i x) C :=
    (hf.tendstoUniformlyOn hC).continuousOn
      (Eventually.of_forall fun s => (continuous_finsetSum s fun i _ => hc i).continuousOn).frequently
  exact hcont.continuousAt hCx

/-- The sum of norms of a locally uniformly summable family of continuous functions is
continuous. -/
theorem LocUnifSummable.continuous_tsum_norm [WeaklyLocallyCompactSpace X] {f : ι → X → ℂ}
    (hf : LocUnifSummable f) (hc : ∀ i, Continuous (f i)) :
    Continuous fun x => ∑' i, ‖f i x‖ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  have hcont : ContinuousOn (fun x => ∑' i, ‖f i x‖) C :=
    (hf.2 C hC).continuousOn
      (Eventually.of_forall fun s =>
        (continuous_finsetSum s fun i _ => (hc i).norm).continuousOn).frequently
  exact hcont.continuousAt hCx

/-- Pulling back along a continuous map. -/
theorem LocUnifSummable.comp {f : ι → X → ℂ} (hf : LocUnifSummable f) {φ : Y → X}
    (hφ : Continuous φ) : LocUnifSummable fun i y => f i (φ y) := by
  refine ⟨fun y => hf.1 (φ y), fun C hC => ?_⟩
  have h := hf.2 (φ '' C) (hC.image hφ)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with s hs y hy
  exact hs (φ y) ⟨y, hy, rfl⟩

/-- The tail of a subfamily along an injection is bounded by the tail of the family. -/
theorem tsum_subfamily_tail_le {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f)
    {e : κ → ι} (he : Function.Injective e) (s : Finset ι) :
    ∑' j, f (e j) - ∑ j ∈ s.preimage e he.injOn, f (e j) ≤ ∑' i, f i - ∑ i ∈ s, f i := by
  have hfe : Summable fun j => f (e j) := hf.comp_injective he
  rw [← hfe.sum_add_tsum_subtype_compl (s.preimage e he.injOn), add_sub_cancel_left,
    ← hf.sum_add_tsum_subtype_compl s, add_sub_cancel_left]
  have hinj : Function.Injective fun j : {j // j ∉ s.preimage e he.injOn} =>
      (⟨e j, fun h => j.property (Finset.mem_preimage.mpr h)⟩ : {i // i ∉ s}) := by
    intro a b hab
    exact Subtype.ext (he (congrArg Subtype.val hab))
  exact tsum_comp_le_tsum_of_inj (hf.subtype _) (fun i => hf0 _) hinj

/-- Restricting to a subfamily along an injection. -/
theorem LocUnifSummable.comp_injective {f : ι → X → ℂ} (hf : LocUnifSummable f) {e : κ → ι}
    (he : Function.Injective e) : LocUnifSummable fun j x => f (e j) x := by
  refine ⟨fun x => (hf.1 x).comp_injective he, fun C hC => ?_⟩
  have h := hf.2 C hC
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hev := h ε hε
  rw [eventually_atTop] at hev ⊢
  obtain ⟨s₀, hs₀⟩ := hev
  refine ⟨s₀.preimage e he.injOn, fun t ht x hx => ?_⟩
  have h1 := hs₀ s₀ le_rfl x hx
  rw [Real.dist_eq] at h1 ⊢
  have hsum := hf.1 x
  have hfe : Summable fun j => ‖f (e j) x‖ := hsum.comp_injective he
  have hle : ∑ j ∈ s₀.preimage e he.injOn, ‖f (e j) x‖ ≤ ∑ j ∈ t, ‖f (e j) x‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg ht fun _ _ _ => norm_nonneg _
  have htail := tsum_subfamily_tail_le (fun i => norm_nonneg (f i x)) hsum he s₀
  have hpos : ∑ j ∈ t, ‖f (e j) x‖ ≤ ∑' j, ‖f (e j) x‖ :=
    hfe.sum_le_tsum t fun _ _ => norm_nonneg _
  have hpos0 : ∑ i ∈ s₀, ‖f i x‖ ≤ ∑' i, ‖f i x‖ := hsum.sum_le_tsum s₀ fun _ _ => norm_nonneg _
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith

end Langlands.Global.RankinSelbergGlobal.Unfolding
