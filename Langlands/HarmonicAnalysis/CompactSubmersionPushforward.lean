import Langlands.HarmonicAnalysis.CompactSubmersionPushforwardStatement
import Langlands.HarmonicAnalysis.LinearBallPushforward
import Langlands.HarmonicAnalysis.UltrametricBallPushforward
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Compact pushforward along nonarchimedean submersions -/

namespace Langlands.HarmonicAnalysis

open Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Topology

universe u uP uX uY

section Local

variable {K P X Y : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup X] [NormedSpace K X] [ProperSpace X]
  [IsUltrametricDist X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [NormedSpace K Y] [FiniteDimensional K Y] [ProperSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

private theorem eventually_map_restrict_of_surjective_partial
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (Φ : P × X → Y) (hΦ : Continuous Φ) (p₀ : P) (a : X)
    (D : P × X →L[K] Y) (hD : HasStrictFDerivAt Φ D (p₀, a))
    (hsurj : Surjective (D.comp (ContinuousLinearMap.inr K P X)))
    {S : Set X} (hS : S ∈ 𝓝 a) :
    ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ S ∧
      ∃ B : Set Y, IsCompact B ∧ IsOpen B ∧ ∃ c : ℝ≥0,
        ∀ᶠ p in 𝓝 p₀, Measure.map (fun x => Φ (p, x)) (μ.restrict (closedBall a r)) =
          c • ν.restrict B := by
  let d := D.comp (ContinuousLinearMap.inr K P X)
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hds (y : Y) : d (s y) = y := DFunLike.congr_fun hs y
  let ε : ℝ≥0 := (‖s‖₊ + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεs : ‖s‖₊ * ε < 1 := by
    rw [show ε = (‖s‖₊ + 1)⁻¹ from rfl, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).mpr (lt_add_one _)
  obtain ⟨W, hW, hApprox⟩ := hD.approximates_deriv_on_nhds (.inr hε)
  obtain ⟨V, hV, T, hT, hVT⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨R, hR, hRT⟩ := Metric.mem_nhds_iff.mp (inter_mem hT hS)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hB : closedBall a r ⊆ T ∩ S := (closedBall_subset_ball (half_lt_self hR)).trans hRT
  let u (p : P) (x : X) : X := s (Φ (p, x) - d x)
  have hLip (p : P) (hp : p ∈ V) : LipschitzOnWith (‖s‖₊ * ε) (u p) (closedBall a r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hApprox (p, x) (hVT ⟨hp, (hB hx).1⟩) (p, y) (hVT ⟨hp, (hB hy).1⟩)
    have hlin : D ((p, x) - (p, y)) = d (x - y) := by
      change D (p - p, x - y) = _
      rw [sub_self]
      rfl
    have hnorm : ‖(p, x) - (p, y)‖ = ‖x - y‖ := by
      change max ‖p - p‖ ‖x - y‖ = _
      rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)]
    have hdiff : Φ (p, x) - d x - (Φ (p, y) - d y) = Φ (p, x) - Φ (p, y) - d (x - y) := by
      rw [map_sub]
      abel
    rw [hlin, hnorm, ← hdiff] at h
    rw [dist_eq_norm, show u p x - u p y = s (Φ (p, x) - d x - (Φ (p, y) - d y)) from
      (s.map_sub _ _).symm]
    exact (s.le_opNorm _).trans (by
      simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm, mul_assoc] using
        mul_le_mul_of_nonneg_left h (norm_nonneg s))
  have hCont (p : P) : Continuous (u p) :=
    s.continuous.comp ((hΦ.comp (continuous_const.prodMk continuous_id)).sub d.continuous)
  have hcenter : Continuous (fun p => a + u p a) :=
    continuous_const.add (s.continuous.comp
      ((hΦ.comp (continuous_id.prodMk continuous_const)).sub continuous_const))
  let b := a + u p₀ a
  have hnear : ∀ᶠ p in 𝓝 p₀, a + u p a ∈ closedBall b r :=
    hcenter.continuousAt.eventually ((IsUltrametricDist.isOpen_closedBall b hr.ne').mem_nhds
      (mem_closedBall_self hr.le))
  obtain ⟨hBc, hBo, c, hc⟩ := map_restrict_closedBall_linear μ ν d hsurj b hr
  refine ⟨r, hr, fun x hx => (hB hx).2, d '' closedBall b r, hBc, hBo, c, ?_⟩
  filter_upwards [hV, hnear] with p hp hpball
  have heq : (fun x => Φ (p, x)) = d ∘ (fun x => x + u p x) := by
    funext x
    change Φ (p, x) = d (x + s (Φ (p, x) - d x))
    rw [map_add, hds]
    abel
  have hmeas : Measurable (fun x => x + u p x) := (continuous_id.add (hCont p)).measurable
  rw [heq, ← Measure.map_map d.continuous.measurable hmeas,
    map_closedBall_add_perturbation μ a hr.le (hLip p hp) hεs (hCont p),
    ← IsUltrametricDist.closedBall_eq_of_mem hpball, hc]

end Local

private theorem exists_disjoint_ball_subcover {X : Type*} [MetricSpace X] [IsUltrametricDist X]
    (S : Set X) (hS : IsCompact S) (r : S → ℝ) (hr : ∀ a, 0 < r a)
    (hsub : ∀ a, closedBall a.val (r a) ⊆ S) :
    ∃ (t : Finset (Set X)) (a : t → S),
      (∀ i, i.val = closedBall (a i).val (r (a i))) ∧
      Pairwise (fun i j : t => Disjoint i.val j.val) ∧
      (⋃ i : t, i.val) = S := by
  classical
  let B (a : S) := closedBall a.val (r a)
  have hcov : S ⊆ ⋃ a : S, B a := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, mem_closedBall_self (hr ⟨x, hx⟩).le⟩
  obtain ⟨c, hc⟩ := hS.elim_finite_subcover B
    (fun a => IsUltrametricDist.isOpen_closedBall a.val (hr a).ne') hcov
  let b := c.image B
  let t := b.filter (fun A => Maximal (· ∈ b) A)
  have hcenter (i : t) : ∃ a : S, i.val = B a := by
    obtain ⟨a, _, h⟩ := Finset.mem_image.mp (Finset.mem_filter.mp i.property).1
    exact ⟨a, h.symm⟩
  choose a ha using hcenter
  refine ⟨t, a, ha, ?_, ?_⟩
  · intro i j hij
    have hi := (Finset.mem_filter.mp i.property).2
    have hj := (Finset.mem_filter.mp j.property).2
    have htrichotomy : i.val ⊆ j.val ∨ j.val ⊆ i.val ∨ Disjoint i.val j.val := by
      rw [ha i, ha j]
      exact IsUltrametricDist.closedBall_subset_trichotomy _ _ _ _
    rcases htrichotomy with h | h | h
    · exact (hij (Subtype.ext (le_antisymm h (hi.2 hj.1 h)))).elim
    · exact (hij (Subtype.ext (le_antisymm (hj.2 hi.1 h) h))).elim
    · exact h
  · apply Subset.antisymm
    · apply iUnion_subset
      intro i
      rw [ha]
      exact hsub _
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
      obtain ⟨hjc, hxj⟩ := mem_iUnion.mp hj
      obtain ⟨A, hja, hm⟩ := b.exists_le_maximal (Finset.mem_image.mpr ⟨j, hjc, rfl⟩)
      exact mem_iUnion.mpr ⟨⟨A, Finset.mem_filter.mpr ⟨hm.1, hm⟩⟩, hja hxj⟩

private noncomputable def clopenDensity {X : Type*} [TopologicalSpace X] {B : Set X}
    (hB : IsClopen B) (c : ℝ≥0) : LocallyConstant X ℝ≥0 :=
  (LocallyConstant.const X c).indicator hB

private theorem withDensity_clopenDensity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    {B : Set X} (hB : IsClopen B) (c : ℝ≥0) :
    μ.withDensity (fun x => (clopenDensity hB c x : ℝ≥0∞)) = c • μ.restrict B := by
  have he : (fun x => (clopenDensity hB c x : ℝ≥0∞)) = B.indicator (fun _ => (c : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, clopenDensity, LocallyConstant.indicator_of_mem _ _ hx]
      rfl
    · rw [Set.indicator_of_notMem hx, clopenDensity, LocallyConstant.indicator_of_notMem _ _ hx]
      rfl
  rw [he, withDensity_indicator hB.2.measurableSet, withDensity_const]
  rfl

private theorem withDensity_sum_locallyConstant {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {ι : Type*} [Fintype ι]
    (μ : Measure X) (g : ι → LocallyConstant X ℝ≥0) :
    μ.withDensity (fun x => ((∑ i, g i) x : ℝ≥0∞)) =
      ∑ i, μ.withDensity (fun x => (g i x : ℝ≥0∞)) := by
  classical
  have he : (fun x => ((∑ i, g i) x : ℝ≥0∞)) = ∑' i, fun x => (g i x : ℝ≥0∞) := by
    funext x
    rw [tsum_fintype, Finset.sum_apply]
    change ENNReal.ofNNRealHom ((LocallyConstant.evalAddMonoidHom x) (∑ i, g i)) = _
    rw [map_sum, map_sum]
    rfl
  rw [he, withDensity_tsum (fun i => (g i).continuous.measurable.coe_nnreal_ennreal),
    Measure.sum_fintype]

/-- A compactly supported locally constant density has one common output density
for all parameters near a submersive slice. -/
theorem compactSubmersionPushforward : CompactSubmersionPushforwardStatement.{u, uP, uX, uY} := by
  classical
  intro K _ _ P _ _ X _ _ _ _ _ _ Y _ _ _ _ _ μ _ ν _ Φ p₀ f hΦ hf hD
  have : ProperSpace X := FiniteDimensional.proper K X
  have : ProperSpace Y := FiniteDimensional.proper K Y
  let S := tsupport (f : X → ℝ≥0)
  have hSupp : S = Function.support (f : X → ℝ≥0) := by
    exact (f.isLocallyConstant.isOpen_fiber (0 : ℝ≥0)).isClosed_compl.closure_eq
  have hlocal (a : S) :
      ∃ r : ℝ, 0 < r ∧ (∀ x ∈ closedBall a.val r, f x = f a.val) ∧
        ∃ B : Set Y, IsCompact B ∧ IsOpen B ∧ ∃ c : ℝ≥0,
          ∀ᶠ p in 𝓝 p₀, Measure.map (fun x => Φ (p, x)) (μ.restrict (closedBall a.val r)) =
            c • ν.restrict B := by
    obtain ⟨D, hD', hs⟩ := hD a a.property
    exact eventually_map_restrict_of_surjective_partial μ ν Φ hΦ p₀ a D hD' hs
      (f.isLocallyConstant.eventually_eq a)
  choose r hr hconst B hBc hBo c hmap using hlocal
  have hsub (a : S) : closedBall a.val (r a) ⊆ S := by
    intro x hx
    rw [hSupp]
    have ha : f a.val ≠ 0 := Function.mem_support.mp (hSupp ▸ a.property)
    exact Function.mem_support.mpr (hconst a x hx ▸ ha)
  obtain ⟨t, a, ha, hpair, hcover⟩ := exists_disjoint_ball_subcover S hf r hr hsub
  have hA (i : t) : IsClopen i.val := by
    rw [ha]
    exact IsUltrametricDist.isClopen_closedBall _ (hr (a i)).ne'
  let fᵢ (i : t) := clopenDensity (hA i) (f (a i).val)
  let gᵢ (i : t) := clopenDensity ⟨(hBc (a i)).isClosed, hBo (a i)⟩ (f (a i).val * c (a i))
  let g := ∑ i, gᵢ i
  have hsum : ∑ i, fᵢ i = f := by
    apply LocallyConstant.ext
    intro x
    change (LocallyConstant.evalAddMonoidHom x) (∑ i, fᵢ i) = f x
    rw [map_sum]
    change ∑ i, fᵢ i x = f x
    by_cases hx : x ∈ S
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
      rw [Finset.sum_eq_single i]
      · change (clopenDensity (hA i) (f (a i).val)) x = f x
        rw [clopenDensity, LocallyConstant.indicator_of_mem _ _ hi]
        exact (hconst (a i) x (ha i ▸ hi)).symm
      · intro j _ hji
        exact LocallyConstant.indicator_of_notMem _ _ fun hj =>
          Set.disjoint_left.mp (hpair hji) hj hi
      · exact fun hi => (hi (Finset.mem_univ i)).elim
    · have hz : f x = 0 := Function.notMem_support.mp (hSupp ▸ hx)
      rw [hz]
      apply Finset.sum_eq_zero
      intro i _
      exact LocallyConstant.indicator_of_notMem _ _ fun hi => hx (hcover ▸ mem_iUnion.mpr ⟨i, hi⟩)
  have hg : HasCompactSupport (g : Y → ℝ≥0) := by
    apply HasCompactSupport.intro (K := ⋃ i : t, B (a i)) (isCompact_iUnion fun i => hBc (a i))
    intro y hy
    change (LocallyConstant.evalAddMonoidHom y) (∑ i, gᵢ i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact LocallyConstant.indicator_of_notMem
      (LocallyConstant.const Y (f (a i).val * c (a i))) ⟨(hBc (a i)).isClosed, hBo (a i)⟩
      (fun h => hy (mem_iUnion.mpr ⟨i, h⟩))
  have hSlice (p : P) : Measurable (fun x => Φ (p, x)) :=
    (hΦ.comp (continuous_const.prodMk continuous_id)).measurable
  have hpieces : ∀ᶠ p in 𝓝 p₀, ∀ i : t,
      Measure.map (fun x => Φ (p, x)) (μ.withDensity (fun x => (fᵢ i x : ℝ≥0∞))) =
        ν.withDensity (fun y => (gᵢ i y : ℝ≥0∞)) := by
    apply eventually_all.mpr
    intro i
    filter_upwards [hmap (a i)] with p hp
    have hμ : μ.withDensity (fun x => (fᵢ i x : ℝ≥0∞)) = f (a i).val • μ.restrict i.val :=
      withDensity_clopenDensity μ (hA i) _
    have hν : ν.withDensity (fun y => (gᵢ i y : ℝ≥0∞)) =
        (f (a i).val * c (a i)) • ν.restrict (B (a i)) :=
      withDensity_clopenDensity ν ⟨(hBc (a i)).isClosed, hBo (a i)⟩ _
    rw [hμ, hν, Measure.map_smul _ (hSlice p).aemeasurable, ha i, hp, smul_smul]
  have hnear : ∀ᶠ p in 𝓝 p₀,
      Measure.map (fun x => Φ (p, x)) (μ.withDensity (fun x => f x)) =
        ν.withDensity (fun y => g y) := by
    filter_upwards [hpieces] with p hp
    rw [← hsum, withDensity_sum_locallyConstant, show g = ∑ i, gᵢ i from rfl,
      withDensity_sum_locallyConstant, Measure.map_finset_sum' (hSlice p).aemeasurable]
    exact Finset.sum_congr rfl fun i _ => hp i
  obtain ⟨U, hUsub, hU, hp₀⟩ := _root_.mem_nhds_iff.mp hnear
  exact ⟨U, hU, hp₀, g, hg, fun p hp => hUsub hp⟩

end Langlands.HarmonicAnalysis
