import Langlands.Geometry.Analytic.Spectrum.Properties
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.Finite

/-! # Finite Laurent inequality neighborhoods in the actual spectrum -/

noncomputable section

universe u

namespace Langlands.Analytic.BanachSpectrum

open Set Filter
open scoped Topology

variable {A : Type u} [NormedCommRing A]

/-- Strict inequalities at a point make a finite closed Laurent locus a
neighborhood of that point. -/
theorem finite_laurentLocus_mem_nhds (x : BanachSpectrum A)
    (s t : Finset A) (r : s → ℝ) (q : t → ℝ)
    (hr : ∀ i, x i.val < r i) (hq : ∀ j, q j < x j.val) :
    laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q ∈ 𝓝 x := by
  simp only [laurentLocus, Set.ofPred_and, Set.ofPred_forall]
  apply Filter.inter_mem
  · apply Filter.iInter_mem.mpr
    intro i
    exact (evaluation i.val).continuous.continuousAt (Iic_mem_nhds (hr i))
  · apply Filter.iInter_mem.mpr
    intro j
    exact (evaluation j.val).continuous.continuousAt (Ici_mem_nhds (hq j))

/-- Every neighborhood in the evaluation topology contains a finite Laurent
locus with positive thresholds and with the point in its interior.
Only the actual spectrum topology and seminorm nonnegativity are used. -/
theorem exists_finite_laurent_neighborhood (x : BanachSpectrum A)
    (U : Set (BanachSpectrum A)) (hU : U ∈ 𝓝 x) :
    ∃ (s t : Finset A) (r : s → ℝ) (q : t → ℝ),
      (∀ i, 0 < r i) ∧ (∀ j, 0 < q j) ∧
      (∀ i, x i.val < r i) ∧ (∀ j, q j < x j.val) ∧
      x ∈ interior (laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q) ∧
      laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q ⊆ U := by
  classical
  rw [evaluation_isEmbedding.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨s, W, hW, hWV⟩ := hV
  have hε : ∀ a : A, ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall (x a) ε ⊆ W a :=
    fun a => Metric.nhds_basis_closedBall.mem_iff.mp (hW a)
  choose ε hεpos hεW using hε
  let t : Finset A := s.filter (fun a => ε a < x a)
  let r : s → ℝ := fun a => x a.val + ε a.val
  let q : t → ℝ := fun a => x a.val - ε a.val
  have hrpos : ∀ i, 0 < r i := fun i =>
    add_pos_of_nonneg_of_pos (apply_nonneg x.toMulRingSeminorm _) (hεpos _)
  have hqpos : ∀ j, 0 < q j := fun j =>
    sub_pos.mpr (Finset.mem_filter.mp j.property).2
  have hr : ∀ i, x i.val < r i := fun i => lt_add_of_pos_right _ (hεpos _)
  have hq : ∀ j, q j < x j.val := fun j => sub_lt_self _ (hεpos _)
  refine ⟨s, t, r, q, hrpos, hqpos, hr, hq,
    mem_interior_iff_mem_nhds.mpr (finite_laurentLocus_mem_nhds x s t r q hr hq), ?_⟩
  intro y hy
  apply hVU
  apply hWV
  intro a ha
  apply hεW a
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  have hu : y a ≤ x a + ε a := hy.1 ⟨a, ha⟩
  have hl : x a - ε a ≤ y a := by
    by_cases h : ε a < x a
    · exact hy.2 ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩⟩
    · have hle := le_of_not_gt h
      have hy0 := apply_nonneg y.toMulRingSeminorm a
      linarith
  constructor <;> linarith

/-- Finite positive-threshold Laurent loci supply compact neighborhoods
inside every prescribed neighborhood. This is a statement about loci, not
an assertion that their analytic-domain factorization has been constructed. -/
theorem exists_compact_finite_laurent_neighborhood (x : BanachSpectrum A)
    (U : Set (BanachSpectrum A)) (hU : U ∈ 𝓝 x) :
    ∃ (s t : Finset A) (r : s → ℝ) (q : t → ℝ),
      (∀ i, 0 < r i) ∧ (∀ j, 0 < q j) ∧
      IsCompact (laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q) ∧
      x ∈ interior (laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q) ∧
      laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q ⊆ U := by
  obtain ⟨s, t, r, q, hr, hq, _, _, hx, hsub⟩ :=
    exists_finite_laurent_neighborhood x U hU
  exact ⟨s, t, r, q, hr, hq, isCompact_laurentLocus _ _ _ _, hx, hsub⟩

end Langlands.Analytic.BanachSpectrum
