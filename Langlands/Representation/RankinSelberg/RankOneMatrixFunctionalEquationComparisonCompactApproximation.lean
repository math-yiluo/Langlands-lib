import Langlands.Representation.Induction.CompactQuotientCutoff
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Compact quotient cutoffs for weighted integral comparisons -/

noncomputable section
open scoped Classical

namespace Langlands.RankinSelberg.CompactWhittakerApproximation

open MeasureTheory Topology Filter Set Induction

universe uG uR uV uA uB

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Exhaustion

variable [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- A compact set of left cosets is contained in a compact clopen set. -/
theorem exists_compactClopen_superset (H : Subgroup G) (hH : IsClosed (H : Set G))
    {K : Set (LeftQuotient H)} (hK : IsCompact K) :
    ∃ C : Set (LeftQuotient H), IsCompact C ∧ IsClopen C ∧ K ⊆ C := by
  classical
  choose C hCc hCcl hyC hCU using fun y : LeftQuotient H =>
    exists_compactClopen_quotientNeighborhood H hH y univ isOpen_univ (mem_univ y)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover C (fun y => (hCcl y).isOpen)
    (fun y _ => mem_iUnion.mpr ⟨y, hyC y⟩)
  exact ⟨⋃ y ∈ t, C y, t.isCompact_biUnion (fun y _ => hCc y),
    isClopen_biUnion_finset (fun y _ => hCcl y), ht⟩

/-- An increasing compact clopen exhaustion of the actual closed-subgroup quotient. -/
theorem exists_compactClopen_exhaustion [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ C : ℕ → Set (LeftQuotient H),
      (∀ n, IsCompact (C n) ∧ IsClopen (C n)) ∧ Monotone C ∧
      ∀ y, ∀ᶠ n in atTop, y ∈ C n := by
  classical
  have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap H
  let : SigmaCompactSpace (LeftQuotient H) := isSigmaCompact_univ_iff.mp (by
    rw [← hq.surjective.range_eq]
    exact isSigmaCompact_range hq.continuous)
  choose D hDc hDcl hKD using fun n : ℕ =>
    exists_compactClopen_superset H hH (isCompact_compactCovering (LeftQuotient H) n)
  refine ⟨accumulate D, fun n => ⟨isCompact_accumulate hDc n,
    (finite_le_nat n).isClopen_biUnion (fun i _ => hDcl i)⟩,
    monotone_accumulate, ?_⟩
  intro y
  obtain ⟨m, hm⟩ := exists_mem_compactCovering y
  filter_upwards [eventually_ge_atTop m] with n hn
  exact mem_iUnion₂.mpr ⟨m, hn, hKD m hm⟩

end Exhaustion

section TopologicalGroup

variable [IsTopologicalGroup G]

section Cutoffs

variable {R : Type uR} {V : Type uV} [CommRing R] [AddCommGroup V] [Module R V]

/-- Compact quotient truncation of an arbitrary smooth induced function. -/
def compactCutoff (H : Subgroup G) (σ : Representation R H V)
    (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C)
    (f : SmoothFunctions H σ) : CompactFunctions H σ :=
  ⟨smoothQuotientCutoff H σ C hc hcl.isOpen f, by
    apply hc.of_isClosed_subset (isClosed_quotientSupport H σ _)
    rw [quotientSupport_smoothQuotientCutoff]
    exact inter_subset_left⟩

@[simp] theorem eval_compactCutoff (H : Subgroup G) (σ : Representation R H V)
    (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C)
    (f : SmoothFunctions H σ) (g : G) :
    eval H σ (compactCutoff H σ C hc hcl f).val g =
      if quotientMap H g ∈ C then eval H σ f g else 0 := rfl

/-- Cutoffs preserve the original values eventually at every group element. -/
theorem eval_compactCutoff_eventually (H : Subgroup G) (σ : Representation R H V)
    (C : ℕ → Set (LeftQuotient H)) (hc : ∀ n, IsCompact (C n))
    (hcl : ∀ n, IsClopen (C n)) (hcover : ∀ y, ∀ᶠ n in atTop, y ∈ C n)
    (f : SmoothFunctions H σ) (g : G) :
    ∀ᶠ n in atTop, eval H σ (compactCutoff H σ (C n) (hc n) (hcl n) f).val g =
      eval H σ f g := by
  filter_upwards [hcover (quotientMap H g)] with n hn
  simp only [eval_compactCutoff, ite_eq_left hn]

end Cutoffs

section WeightedIntegrals

variable {A : Type uA} [MeasurableSpace A] (μ : Measure A)
    (H : Subgroup G) (σ : Representation ℂ H ℂ)
    (C : ℕ → Set (LeftQuotient H)) (hc : ∀ n, IsCompact (C n))
    (hcl : ∀ n, IsClopen (C n))
    (f : SmoothFunctions H σ) (ρ : A → G) (w : A → ℂ)

omit [MeasurableSpace A] in
/-- The weighted cutoff is the measurable indicator of the pulled-back quotient set. -/
theorem weighted_compactCutoff_eq_indicator (n : ℕ) :
    (fun a => w a *
      eval H σ (compactCutoff H σ (C n) (hc n) (hcl n) f).val (ρ a)) =
    (ρ ⁻¹' (quotientMap H ⁻¹' C n)).indicator (fun a => w a * eval H σ f (ρ a)) := by
  funext a
  simp only [eval_compactCutoff, Set.indicator_apply, Set.mem_preimage,
    mul_ite, mul_zero]

omit [MeasurableSpace A] in
/-- Cutoffs dominate every weighted pullback by the norm of the original integrand. -/
theorem norm_weighted_compactCutoff_le (n : ℕ) (a : A) :
    ‖w a * eval H σ (compactCutoff H σ (C n) (hc n) (hcl n) f).val (ρ a)‖ ≤
      ‖w a * eval H σ f (ρ a)‖ := by
  rw [eval_compactCutoff]
  split_ifs
  · exact le_rfl
  · simpa only [mul_zero, norm_zero] using
      (norm_nonneg (w a * eval H σ f (ρ a)))

variable [MeasurableSpace G] [BorelSpace G]

/-- Genuine weighted integrability is preserved by compact quotient truncation. -/
theorem weighted_compactCutoff_integrable (hρ : Measurable ρ)
    (hi : Integrable (fun a => w a * eval H σ f (ρ a)) μ) (n : ℕ) :
    Integrable (fun a => w a *
      eval H σ (compactCutoff H σ (C n) (hc n) (hcl n) f).val (ρ a)) μ := by
  rw [weighted_compactCutoff_eq_indicator]
  exact hi.indicator
    (((hcl n).isOpen.preimage
      (QuotientIntegration.leftQuotient_isOpenQuotientMap H).continuous).measurableSet.preimage hρ)

/-- Weighted integrals of the actual compact induced cutoffs converge with the
same supplied measure, assuming genuine integrability of the limiting integrand. -/
theorem weighted_compactCutoff_integral_tendsto
    (hcover : ∀ y, ∀ᶠ n in atTop, y ∈ C n) (hρ : Measurable ρ)
    (hi : Integrable (fun a => w a * eval H σ f (ρ a)) μ) :
    Tendsto (fun n => ∫ a, w a *
      eval H σ (compactCutoff H σ (C n) (hc n) (hcl n) f).val (ρ a) ∂μ)
      atTop (𝓝 (∫ a, w a * eval H σ f (ρ a) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun a => ‖w a * eval H σ f (ρ a)‖)
  · intro n
    exact (weighted_compactCutoff_integrable μ H σ C hc hcl f ρ w hρ hi n).aestronglyMeasurable
  · exact hi.norm
  · intro n
    exact ae_of_all _ (norm_weighted_compactCutoff_le H σ C hc hcl f ρ w n)
  · apply ae_of_all
    intro a
    apply tendsto_const_nhds.congr'
    filter_upwards [eval_compactCutoff_eventually H σ C hc hcl hcover f (ρ a)] with n hn
    rw [hn]

end WeightedIntegrals

end TopologicalGroup

section Comparison

variable [NonarchimedeanGroup G] [LocallyCompactSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : Type uA} {B : Type uB} [MeasurableSpace A] [MeasurableSpace B]

/-- An identity of two weighted integrals for all compact induced functions
extends to any smooth induced function whose two weighted pullbacks are integrable. -/
theorem weighted_integral_eq_of_compact (μ : Measure A) (ν : Measure B)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (σ : Representation ℂ H ℂ)
    (ρ : A → G) (τ : B → G) (w : A → ℂ) (v : B → ℂ)
    (hρ : Measurable ρ) (hτ : Measurable τ)
    (hcompact : ∀ f : CompactFunctions H σ,
      (∫ a, w a * eval H σ f.val (ρ a) ∂μ) =
      ∫ b, v b * eval H σ f.val (τ b) ∂ν)
    (f : SmoothFunctions H σ)
    (hi : Integrable (fun a => w a * eval H σ f (ρ a)) μ)
    (hj : Integrable (fun b => v b * eval H σ f (τ b)) ν) :
    (∫ a, w a * eval H σ f (ρ a) ∂μ) =
      ∫ b, v b * eval H σ f (τ b) ∂ν := by
  obtain ⟨C, hC, _, hcover⟩ := exists_compactClopen_exhaustion H hH
  have hleft := weighted_compactCutoff_integral_tendsto μ H σ C
    (fun n => (hC n).1) (fun n => (hC n).2) f ρ w hcover hρ hi
  have hright := weighted_compactCutoff_integral_tendsto ν H σ C
    (fun n => (hC n).1) (fun n => (hC n).2) f τ v hcover hτ hj
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Eventually.of_forall (fun n =>
    (hcompact (compactCutoff H σ (C n) (hC n).1 (hC n).2 f)).symm)

end Comparison

end Langlands.RankinSelberg.CompactWhittakerApproximation
