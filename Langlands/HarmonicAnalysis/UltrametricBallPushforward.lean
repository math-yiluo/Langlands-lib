import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Contracting

/-! # Haar measure under a small perturbation of an ultrametric ball -/

namespace Langlands.HarmonicAnalysis

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {X : Type*} [NormedAddCommGroup X]

private theorem dist_add_perturbation [IsUltrametricDist X] {S : Set X} {u : X → X} {c : ℝ≥0}
    (hu : LipschitzOnWith c u S) (hc : c < 1) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    dist (x + u x) (y + u y) = dist x y := by
  by_cases hxy : x = y
  · simp [hxy]
  have hc' : (c : ℝ) < 1 := by exact_mod_cast hc
  have hlt : dist (u x) (u y) < dist x y :=
    (hu.dist_le_mul x hx y hy).trans_lt (mul_lt_of_lt_one_left (dist_pos.mpr hxy) hc')
  simp only [dist_eq_norm] at hlt ⊢
  rw [add_sub_add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
    max_eq_left hlt.le]

private theorem image_closedBall_add_perturbation [IsUltrametricDist X] [CompleteSpace X]
    (a : X) {r : ℝ} (hr : 0 ≤ r) {u : X → X} {c : ℝ≥0}
    (hu : LipschitzOnWith c u (closedBall a r)) (hc : c < 1) :
    (fun x => x + u x) '' closedBall a r = closedBall (a + u a) r := by
  have ha : a ∈ closedBall a r := mem_closedBall_self hr
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall.mpr (by rw [dist_add_perturbation hu hc hx ha]; exact hx)
  intro b hb
  let t : X → X := fun x => b - u x
  have ht : LipschitzOnWith c t (closedBall a r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have he : t x - t y = -(u x - u y) := by
      dsimp only [t]
      abel
    rw [dist_eq_norm, he, norm_neg, ← dist_eq_norm]
    exact hu.dist_le_mul x hx y hy
  have hmaps : MapsTo t (closedBall a r) (closedBall a r) := by
    intro x hx
    have hbound : dist (u x) (u a) ≤ r :=
      (hu.dist_le_mul x hx a ha).trans
        ((mul_le_of_le_one_left dist_nonneg (by exact_mod_cast hc.le)).trans hx)
    have he : t x - a = (b - (a + u a)) + -(u x - u a) := by
      dsimp only [t]
      abel
    rw [mem_closedBall, dist_eq_norm, he]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by rwa [← dist_eq_norm]) (by simpa only [norm_neg, ← dist_eq_norm] using hbound))
  obtain ⟨x, hx, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    (K := c) (f := t) isClosed_closedBall.isComplete hmaps
    ⟨hc, ht.to_restrict⟩ ha (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  have hfix' : b - u x = x := hfix
  exact (sub_eq_iff_eq_add.mp hfix').symm

private theorem measure_ext_closedBalls [IsUltrametricDist X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ]
    (h : ∀ (x : X) (r : ℝ), 0 < r → μ (closedBall x r) = ν (closedBall x r)) : μ = ν := by
  let S : Set (Set X) := {s | ∃ x : X, ∃ r : ℝ, 0 < r ∧ s = closedBall x r}
  have hBasis : IsTopologicalBasis S := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨x, r, hr, rfl⟩
      exact IsUltrametricDist.isOpen_closedBall x hr.ne'
    · intro x U hx hU
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
      exact ⟨closedBall x (r / 2), ⟨x, r / 2, half_pos hr, rfl⟩,
        mem_closedBall_self (half_pos hr).le, (closedBall_subset_ball (half_lt_self hr)).trans hsub⟩
  have hPi : IsPiSystem S := by
    rintro s ⟨x, r, hr, rfl⟩ t ⟨y, u, hu, rfl⟩ hst
    rcases IsUltrametricDist.closedBall_subset_trichotomy x y r u with hsub | hsub | hd
    · exact ⟨x, r, hr, inter_eq_left.mpr hsub⟩
    · exact ⟨y, u, hu, inter_eq_right.mpr hsub⟩
    · rw [Set.disjoint_iff_inter_eq_empty.mp hd] at hst
      exact (Set.not_nonempty_empty hst).elim
  let B (j : ℕ) := closedBall (0 : X) (j + 1 : ℝ)
  apply Measure.ext_of_generateFrom_of_iUnion S B
    ((BorelSpace.measurable_eq (α := X)).trans hBasis.borel_eq_generateFrom) hPi
  · apply eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.mpr ⟨j, mem_closedBall.mpr (show dist x 0 ≤ (j : ℝ) + 1 by linarith)⟩
  · exact fun j => ⟨0, j + 1, by positivity, rfl⟩
  · exact fun j => (measure_lt_top μ (B j)).ne
  · rintro s ⟨x, r, hr, rfl⟩
    exact h x r hr

/-- On an ultrametric ball, adding a perturbation with Lipschitz constant strictly
less than one transports restricted additive Haar to the ball of the same radius
about the new center. -/
theorem map_closedBall_add_perturbation [IsUltrametricDist X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] (a : X) {r : ℝ} (hr : 0 ≤ r)
    {u : X → X} {c : ℝ≥0} (hu : LipschitzOnWith c u (closedBall a r)) (hc : c < 1)
    (hcont : Continuous u) :
    Measure.map (fun x => x + u x) (μ.restrict (closedBall a r)) =
      μ.restrict (closedBall (a + u a) r) := by
  let F : X → X := fun x => x + u x
  have hF : Measurable F := (continuous_id.add hcont).measurable
  have hIm : F '' closedBall a r = closedBall (F a) r :=
    image_closedBall_add_perturbation a hr hu hc
  have hRestr : IsFiniteMeasure (μ.restrict (closedBall a r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall a r).measure_lt_top⟩
  apply measure_ext_closedBalls
  intro y t _
  rw [Measure.map_apply hF isClosed_closedBall.measurableSet,
    Measure.restrict_apply (hF isClosed_closedBall.measurableSet),
    Measure.restrict_apply isClosed_closedBall.measurableSet]
  rcases (closedBall y t ∩ closedBall (F a) r).eq_empty_or_nonempty with hEmpty | ⟨z, hz, hza⟩
  · have hpre : F ⁻¹' closedBall y t ∩ closedBall a r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxa⟩
      have hi : F x ∈ closedBall (F a) r := hIm ▸ ⟨x, hxa, rfl⟩
      exact notMem_empty (F x) (hEmpty ▸ ⟨hx, hi⟩)
    rw [hpre, hEmpty]
  · obtain ⟨b, hb, rfl⟩ : z ∈ F '' closedBall a r := hIm.symm ▸ hza
    have hy : closedBall y t = closedBall (F b) t := IsUltrametricDist.closedBall_eq_of_mem hz
    have hFa : closedBall (F a) r = closedBall (F b) r :=
      IsUltrametricDist.closedBall_eq_of_mem hza
    have hab : closedBall a r = closedBall b r := IsUltrametricDist.closedBall_eq_of_mem hb
    have hPre : F ⁻¹' closedBall y t ∩ closedBall a r = closedBall b (min t r) := by
      ext x
      simp only [hy, mem_inter_iff, mem_preimage, mem_closedBall, le_min_iff]
      constructor
      · rintro ⟨hx, hxa⟩
        rw [dist_add_perturbation hu hc hxa hb] at hx
        exact ⟨hx, mem_closedBall.mp (hab ▸ (show x ∈ closedBall a r from hxa))⟩
      · rintro ⟨hx, hxb⟩
        have hxa : x ∈ closedBall a r := hab.symm ▸ (show x ∈ closedBall b r from hxb)
        rw [dist_add_perturbation hu hc hxa hb]
        exact ⟨hx, hxa⟩
    have hPost : closedBall y t ∩ closedBall (F a) r = closedBall (F b) (min t r) := by
      rw [hy, hFa]
      ext x
      simp
    rw [hPre, hPost, Measure.addHaar_closedBall_center μ b, Measure.addHaar_closedBall_center μ (F b)]

end Langlands.HarmonicAnalysis
