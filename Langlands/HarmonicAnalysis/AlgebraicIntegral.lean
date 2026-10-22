import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Algebraic integration of finite-image functions -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Langlands.HarmonicAnalysis.AlgebraicIntegral

universe u v w z

variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]
variable {μ : Measure X}

/-- The finite fiber sum, with real measures embedded in the complex scalars. -/
def integral (μ : Measure X) (f : SimpleFunc X V) : V :=
  ∑ v ∈ f.range, ((μ (f ⁻¹' {v})).toReal : ℂ) • v

/-- Enlarging the value list, or omitting its zero value, does not change the sum. -/
theorem integral_eq_sum_of_subset (f : SimpleFunc X V) (s : Finset V)
    (hs : ∀ v ∈ f.range, v ≠ 0 → v ∈ s) :
    integral μ f = ∑ v ∈ s, ((μ (f ⁻¹' {v})).toReal : ℂ) • v := by
  classical
  have hz (v : V) (hv : v ∉ f.range) :
      ((μ (f ⁻¹' {v})).toReal : ℂ) • v = 0 := by
    rw [(f.preimage_eq_empty_iff v).2 hv]
    simp
  calc
    integral μ f = ∑ v ∈ f.range.filter (· ≠ 0),
        ((μ (f ⁻¹' {v})).toReal : ℂ) • v := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro v hv h
      have : v = 0 := by simpa [hv] using h
      simp [this]
    _ = ∑ v ∈ s, ((μ (f ⁻¹' {v})).toReal : ℂ) • v := by
      apply Finset.sum_subset
      · intro v hv
        exact hs v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
      · intro v hv h
        by_cases hv0 : v = 0
        · simp [hv0]
        · exact hz v (fun hvr => h (Finset.mem_filter.mpr ⟨hvr, hv0⟩))

@[simp] theorem integral_zero : integral μ (0 : SimpleFunc X V) = 0 := by
  rw [integral_eq_sum_of_subset _ ∅]
  · simp
  · intro v hv h
    exact (h (SimpleFunc.eq_zero_of_mem_range_zero hv)).elim

/-- Regrouping fibers is valid for every zero-preserving map; linearity is not assumed. -/
theorem integral_map {A : Type z} [Zero A] (f : SimpleFunc X A)
    (hf : f.FinMeasSupp μ) (g : A → V) (hg : g 0 = 0) :
    integral μ (f.map g) = ∑ a ∈ f.range, ((μ (f ⁻¹' {a})).toReal : ℂ) • g a := by
  classical
  simp only [integral, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  by_cases hb0 : g b = 0
  · simp only [hb0, smul_zero]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [(Finset.mem_filter.mp ha).2, smul_zero]
  · have hfinite : ∀ a ∈ f.range.filter (fun a => g a = g b),
        μ (f ⁻¹' {a}) ≠ ⊤ := by
      intro a ha
      apply (hf.meas_preimage_singleton_ne_zero ?_).ne
      intro ha0
      exact hb0 ((Finset.mem_filter.mp ha).2.symm.trans (ha0 ▸ hg))
    rw [SimpleFunc.map_preimage_singleton, ← f.sum_measure_preimage_singleton,
      ENNReal.toReal_sum hfinite, Complex.ofReal_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]

/-- Additivity follows by refining to the joint fibers of the two functions. -/
theorem integral_add (f g : SimpleFunc X V) (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : integral μ (f + g) = integral μ f + integral μ g := by
  rw [SimpleFunc.add_eq_map₂, integral_map _ (hf.pair hg) _ (by simp)]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  rw [← integral_map _ (hf.pair hg) Prod.fst rfl,
    ← integral_map _ (hf.pair hg) Prod.snd rfl]
  rfl

/-- Arbitrary complex linear maps commute with the finite fiber sum. -/
theorem integral_linearMap (f : SimpleFunc X V) (hf : f.FinMeasSupp μ)
    (L : V →ₗ[ℂ] W) : integral μ (f.map L) = L (integral μ f) := by
  rw [integral_map _ hf _ L.map_zero]
  simp [integral, map_sum]

/-- Complex homogeneity. -/
theorem integral_smul (c : ℂ) (f : SimpleFunc X V) (hf : f.FinMeasSupp μ) :
    integral μ (c • f) = c • integral μ f := by
  change integral μ (f.map (c • ·)) = _
  rw [integral_map _ hf _ (smul_zero c)]
  simp only [integral, Finset.smul_sum, smul_comm c]

/-- Simple functions with finite-measure support form a complex submodule. -/
def finiteSupportSubmodule (μ : Measure X) : Submodule ℂ (SimpleFunc X V) where
  carrier := {f | f.FinMeasSupp μ}
  zero_mem' := by simp [SimpleFunc.finMeasSupp_iff_support]
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.map (smul_zero c)

/-- Integration as a complex linear map, with all laws derived from the fiber sum. -/
def integralLinear (μ : Measure X) : finiteSupportSubmodule (V := V) μ →ₗ[ℂ] V where
  toFun f := integral μ f.val
  map_add' f g := integral_add f.val g.val f.property g.property
  map_smul' c f := integral_smul c f.val f.property

/-- Finite sums preserve finite-measure support. -/
theorem finMeasSupp_sum {I : Type*} (s : Finset I) (f : I → SimpleFunc X V)
    (hf : ∀ i ∈ s, (f i).FinMeasSupp μ) : (∑ i ∈ s, f i).FinMeasSupp μ :=
  (finiteSupportSubmodule μ).sum_mem hf

/-- Integration commutes with finite sums of functions with finite-measure support. -/
theorem integral_sum {I : Type*} (s : Finset I) (f : I → SimpleFunc X V)
    (hf : ∀ i ∈ s, (f i).FinMeasSupp μ) :
    integral μ (∑ i ∈ s, f i) = ∑ i ∈ s, integral μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, integral_add]
    · rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    · exact hf i (Finset.mem_insert_self _ _)
    · exact finMeasSupp_sum s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- An indicator constant integrates to its measure times its value. This formula
also records the totalized convention when the set has infinite measure. -/
theorem integral_indicator_const (s : Set X) (hs : MeasurableSet s) (v : V) :
    integral μ ((SimpleFunc.const X v).restrict s) = ((μ s).toReal : ℂ) • v := by
  classical
  by_cases hv : v = 0
  · subst v
    have hz : (SimpleFunc.const X (0 : V)).restrict s = 0 := by
      ext x
      simp [SimpleFunc.restrict_apply _ hs]
    rw [hz]
    simp
  · rw [integral_eq_sum_of_subset _ {v}]
    · simp only [Finset.sum_singleton]
      rw [SimpleFunc.restrict_preimage_singleton _ hs hv]
      have he : (SimpleFunc.const X v) ⁻¹' {v} = Set.univ := by ext; simp
      rw [he, Set.inter_univ]
    · intro w hw hw0
      obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hw
      rw [SimpleFunc.restrict_apply _ hs] at hx
      by_cases hxs : x ∈ s
      · simpa [Set.indicator_of_mem hxs] using hx.symm
      · simp [Set.indicator_of_notMem hxs] at hx
        exact (hw0 hx.symm).elim

omit [Module ℂ V] in
/-- Only nonzero indicator values require finite measure. -/
theorem finMeasSupp_indicator_const (s : Set X) (hs : MeasurableSet s) (v : V)
    (hfinite : v ≠ 0 → μ s < ⊤) : ((SimpleFunc.const X v).restrict s).FinMeasSupp μ := by
  rw [SimpleFunc.finMeasSupp_iff_support]
  by_cases hv : v = 0
  · subst v
    have hz : (SimpleFunc.const X (0 : V)).restrict s = 0 := by
      ext x
      simp [SimpleFunc.restrict_apply _ hs]
    rw [hz]
    simp
  · apply lt_of_le_of_lt (measure_mono ?_) (hfinite hv)
    intro x hx
    by_contra hxs
    exact hx (by simp [SimpleFunc.restrict_apply _ hs, hxs])

/-- A finite indicator presentation computes the integral. This includes finite
measurable partitions, overlaps with summing values, and all their refinements. -/
theorem integral_eq_of_indicator_presentation {I : Type*} (t : Finset I)
    (s : I → Set X) (v : I → V) (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hfinite : ∀ i ∈ t, v i ≠ 0 → μ (s i) < ⊤) (f : SimpleFunc X V)
    (hpres : ∀ x, f x = ∑ i ∈ t, (s i).indicator (fun _ => v i) x) :
    integral μ f = ∑ i ∈ t, ((μ (s i)).toReal : ℂ) • v i := by
  have heq : f = ∑ i ∈ t, (SimpleFunc.const X (v i)).restrict (s i) := by
    ext x
    rw [hpres]
    let ev : SimpleFunc X V →+ V :=
      { toFun := fun g => g x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change _ = ev (∑ i ∈ t, (SimpleFunc.const X (v i)).restrict (s i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (SimpleFunc.restrict_apply (SimpleFunc.const X (v i)) (hs i hi) x).symm
  rw [heq, integral_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_indicator_const (s i) (hs i hi) (v i)
  · intro i hi
    exact finMeasSupp_indicator_const (s i) (hs i hi) (v i) (hfinite i hi)

/-- A disjoint measurable partition of the support gives the expected weighted
sum. Zero-valued cells may have infinite measure and points outside the cells
are permitted when the function is zero there. -/
theorem integral_eq_of_partition {I : Type*} (t : Finset I)
    (s : I → Set X) (v : I → V) (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hfinite : ∀ i ∈ t, v i ≠ 0 → μ (s i) < ⊤) (f : SimpleFunc X V)
    (hdisjoint : (↑t : Set I).PairwiseDisjoint s)
    (hcover : Function.support f ⊆ ⋃ i ∈ t, s i)
    (hvalue : ∀ i ∈ t, ∀ x ∈ s i, f x = v i) :
    integral μ f = ∑ i ∈ t, ((μ (s i)).toReal : ℂ) • v i := by
  classical
  apply integral_eq_of_indicator_presentation t s v hs hfinite f
  intro x
  by_cases hx : ∃ i ∈ t, x ∈ s i
  · obtain ⟨i, hi, hxi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hxi, hvalue i hi x hxi]
    · intro j hj hji
      apply Set.indicator_of_notMem
      intro hxj
      exact Set.disjoint_left.mp (hdisjoint hj hi hji) hxj hxi
    · exact fun h => (h hi).elim
  · have hfzero : f x = 0 := by
      by_contra h
      have := hcover h
      exact hx (by simpa only [Set.mem_iUnion, exists_prop] using this)
    rw [hfzero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact Set.indicator_of_notMem (fun h => hx ⟨i, hi, h⟩) _

/-- Any two finite measurable indicator presentations of the same function give
the same weighted sum. In particular this proves invariance under refinement. -/
theorem presentation_independent {I J : Type*} (t : Finset I) (r : Finset J)
    (s : I → Set X) (q : J → Set X) (v : I → V) (w : J → V)
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (hq : ∀ j ∈ r, MeasurableSet (q j))
    (hfinite : ∀ i ∈ t, v i ≠ 0 → μ (s i) < ⊤)
    (hfinite' : ∀ j ∈ r, w j ≠ 0 → μ (q j) < ⊤) (f : SimpleFunc X V)
    (hpres : ∀ x, f x = ∑ i ∈ t, (s i).indicator (fun _ => v i) x)
    (hpres' : ∀ x, f x = ∑ j ∈ r, (q j).indicator (fun _ => w j) x) :
    (∑ i ∈ t, ((μ (s i)).toReal : ℂ) • v i) =
      ∑ j ∈ r, ((μ (q j)).toReal : ℂ) • w j :=
  (integral_eq_of_indicator_presentation t s v hs hfinite f hpres).symm.trans
    (integral_eq_of_indicator_presentation r q w hq hfinite' f hpres')

/-- The complex-valued construction is the genuine Bochner integral. -/
theorem integral_eq_bochner (f : SimpleFunc X ℂ) (hf : f.FinMeasSupp μ) :
    integral μ f = ∫ x, f x ∂μ := by
  rw [f.integral_eq_sum hf.integrable]
  simp only [integral, measureReal_def, Complex.real_smul, smul_eq_mul]

/-- Change of variables for a measurable map and its pushforward measure. -/
theorem integral_comp {Y : Type z} [MeasurableSpace Y] (f : SimpleFunc Y V)
    (e : X → Y) (he : Measurable e) :
    integral μ (f.comp e he) = integral (Measure.map e μ) f := by
  rw [integral_eq_sum_of_subset _ f.range]
  · unfold integral
    apply Finset.sum_congr rfl
    intro v hv
    rw [Measure.map_apply he (f.measurableSet_fiber v)]
    rfl
  · intro v hv _
    exact f.range_comp_subset_range he hv

/-- Measure-preserving change of variables; in particular it applies to
measure-preserving measurable equivalences without sigma-finiteness. -/
theorem integral_comp_measurePreserving {Y : Type z} [MeasurableSpace Y]
    {ν : Measure Y} (f : SimpleFunc Y V) (e : X → Y)
    (he : MeasurePreserving e μ ν) :
    integral μ (f.comp e he.measurable) = integral ν f := by
  rw [integral_comp, he.map_eq]

omit [Module ℂ V] in
/-- Finite-measure support is preserved by measure-preserving pullback. -/
theorem finMeasSupp_comp_measurePreserving {Y : Type z} [MeasurableSpace Y]
    {ν : Measure Y} (f : SimpleFunc Y V) (e : X → Y)
    (he : MeasurePreserving e μ ν) :
    (f.comp e he.measurable).FinMeasSupp μ ↔ f.FinMeasSupp ν := by
  change μ (e ⁻¹' Function.support f) < ⊤ ↔ ν (Function.support f) < ⊤
  rw [he.measure_preimage f.measurableSet_support.nullMeasurableSet]

end Langlands.HarmonicAnalysis.AlgebraicIntegral
