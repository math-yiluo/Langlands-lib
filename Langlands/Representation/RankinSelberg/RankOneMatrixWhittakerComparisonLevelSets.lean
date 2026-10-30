import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite level-set expansions of locally constant families

A function on a topological space that is locally constant and constant off a
compact set takes finitely many values. For a family `H : Y → X → ℂ` with finitely
many values and measurable fibres, the product integral of `H y x * h x` is the
finite sum over the values `v` of `ν(H⁻¹ v) * ∫ v h dμ`, and integrability passes
between the product and the fibres of positive measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory
open scoped ENNReal

section Topology

variable {Y β : Type*} [TopologicalSpace Y]

/-- A function invariant under right translation by an open neighbourhood of `1`
is locally constant. -/
theorem isLocallyConstant_of_mul_right_invariant [Group Y] [ContinuousMul Y] {H : Y → β}
    {U : Set Y} (hU : IsOpen U) (h1 : (1 : Y) ∈ U) (hH : ∀ y, ∀ u ∈ U, H (y * u) = H y) :
    IsLocallyConstant H := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  refine ⟨(y * ·) '' U, isOpenMap_mul_left y U hU, ⟨1, h1, mul_one y⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hH y u hu

/-- A locally constant function that is constant off a compact set has finite range. -/
theorem finite_range_of_isLocallyConstant {H : Y → β} (hH : IsLocallyConstant H)
    {C : Set Y} (hC : IsCompact C) {b : β} (hout : ∀ y ∉ C, H y = b) :
    (Set.range H).Finite := by
  let : TopologicalSpace β := ⊥
  have : DiscreteTopology β := ⟨rfl⟩
  refine ((hC.image hH.continuous).finite_of_discrete.union (Set.finite_singleton b)).subset ?_
  rintro _ ⟨y, rfl⟩
  by_cases hy : y ∈ C
  · exact Or.inl ⟨y, hy, rfl⟩
  · exact Or.inr (hout y hy)

/-- The fibres of a locally constant function are measurable. -/
theorem measurableSet_fiber_of_isLocallyConstant [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {H : Y → β} (hH : IsLocallyConstant H) (v : β) : MeasurableSet (H ⁻¹' {v}) :=
  (hH.isOpen_fiber v).measurableSet

end Topology

section Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A family with finitely many values is the sum over its values of the fibre
indicators times the values. -/
theorem eq_sum_levelSets {H : Y → X → ℂ} (hfin : (Set.range H).Finite) (y : Y) (x : X) :
    H y x = ∑ v ∈ hfin.toFinset, (H ⁻¹' {v}).indicator (1 : Y → ℂ) y * v x := by
  rw [Finset.sum_eq_single (H y)]
  · rw [Set.indicator_of_mem (show y ∈ H ⁻¹' {H y} from rfl), Pi.one_apply, one_mul]
  · intro v _ hv
    rw [Set.indicator_of_notMem (show y ∉ H ⁻¹' {v} from fun h => hv h.symm), zero_mul]
  · intro h
    exact absurd (hfin.mem_toFinset.2 ⟨y, rfl⟩) h

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The part of the product integrand over one fibre. -/
theorem levelSet_term_eq_indicator {H : Y → X → ℂ} (h : X → ℂ) (v : X → ℂ) :
    (fun p : X × Y => (v p.1 * h p.1) * (H ⁻¹' {v}).indicator (1 : Y → ℂ) p.2) =
      (Set.univ ×ˢ (H ⁻¹' {v})).indicator (fun p : X × Y => H p.2 p.1 * h p.1) := by
  funext p
  by_cases hp : H p.2 = v
  · rw [Set.indicator_of_mem (show p ∈ Set.univ ×ˢ (H ⁻¹' {v}) from ⟨trivial, hp⟩),
      Set.indicator_of_mem (show p.2 ∈ H ⁻¹' {v} from hp), hp, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show p ∉ Set.univ ×ˢ (H ⁻¹' {v}) from fun h => hp h.2),
      Set.indicator_of_notMem (show p.2 ∉ H ⁻¹' {v} from hp), mul_zero]

/-- **Finite level-set expansion of a product integral.** -/
theorem integral_prod_eq_sum_levelSets [SFinite μ] [SFinite ν] {H : Y → X → ℂ}
    (hfin : (Set.range H).Finite) (hmeas : ∀ v, MeasurableSet (H ⁻¹' {v})) (h : X → ℂ)
    (hint : Integrable (fun p : X × Y => H p.2 p.1 * h p.1) (μ.prod ν)) :
    ∫ p, H p.2 p.1 * h p.1 ∂(μ.prod ν) =
      ∑ v ∈ hfin.toFinset, ν.real (H ⁻¹' {v}) * ∫ x, v x * h x ∂μ := by
  have hterm : ∀ v, Integrable (fun p : X × Y =>
      (v p.1 * h p.1) * (H ⁻¹' {v}).indicator (1 : Y → ℂ) p.2) (μ.prod ν) := by
    intro v
    rw [levelSet_term_eq_indicator]
    exact hint.indicator (MeasurableSet.univ.prod (hmeas v))
  calc ∫ p, H p.2 p.1 * h p.1 ∂(μ.prod ν)
      = ∫ p, ∑ v ∈ hfin.toFinset,
          (v p.1 * h p.1) * (H ⁻¹' {v}).indicator (1 : Y → ℂ) p.2 ∂(μ.prod ν) := by
        congr 1
        funext p
        rw [eq_sum_levelSets hfin p.2 p.1, Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ = ∑ v ∈ hfin.toFinset, ∫ p,
          (v p.1 * h p.1) * (H ⁻¹' {v}).indicator (1 : Y → ℂ) p.2 ∂(μ.prod ν) :=
        integral_finsetSum _ fun v _ => hterm v
    _ = ∑ v ∈ hfin.toFinset, ν.real (H ⁻¹' {v}) * ∫ x, v x * h x ∂μ := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [integral_prod_mul (fun x => v x * h x) ((H ⁻¹' {v}).indicator (1 : Y → ℂ)),
          integral_indicator (hmeas v), mul_comm]
        simp only [Pi.one_apply, setIntegral_const, Complex.real_smul, mul_one]

/-- **Integrability of a fibre value.** If the product integrand is integrable and a
value is taken on a set of positive measure, that value times `h` is integrable. -/
theorem integrable_of_integrable_prod_levelSet [SFinite μ] [SFinite ν] {H : Y → X → ℂ}
    (h : X → ℂ) (hint : Integrable (fun p : X × Y => H p.2 p.1 * h p.1) (μ.prod ν))
    {v : X → ℂ} (hv : ν (H ⁻¹' {v}) ≠ 0) : Integrable (fun x => v x * h x) μ := by
  obtain ⟨y, hy, hyint⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hv (ae_restrict_of_ae hint.prod_left_ae)
  have hy' : H y = v := hy
  simpa only [hy'] using hyint

/-- **Integrability from the values.** If every nonzero value is taken on a set of
finite measure and is integrable against `h`, the product integrand is integrable. -/
theorem integrable_prod_of_levelSets [SFinite ν] {H : Y → X → ℂ}
    (hfin : (Set.range H).Finite) (hmeas : ∀ v, MeasurableSet (H ⁻¹' {v})) (h : X → ℂ)
    (hv : ∀ v ∈ Set.range H, v ≠ 0 →
      ν (H ⁻¹' {v}) ≠ ∞ ∧ Integrable (fun x => v x * h x) μ) :
    Integrable (fun p : X × Y => H p.2 p.1 * h p.1) (μ.prod ν) := by
  have hsum : (fun p : X × Y => H p.2 p.1 * h p.1) = fun p => ∑ v ∈ hfin.toFinset,
      (v p.1 * h p.1) * (H ⁻¹' {v}).indicator (1 : Y → ℂ) p.2 := by
    funext p
    rw [eq_sum_levelSets hfin p.2 p.1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsum]
  refine integrable_finsetSum _ fun v hv' => ?_
  by_cases h0 : v = 0
  · subst h0
    simp only [Pi.zero_apply, zero_mul]
    exact integrable_zero _ _ _
  · obtain ⟨hfinite, hvint⟩ := hv v (hfin.mem_toFinset.1 hv') h0
    exact hvint.mul_prod ((integrable_indicator_iff (hmeas v)).2 (integrableOn_const hfinite))

end Measure

end Langlands.RankinSelberg
