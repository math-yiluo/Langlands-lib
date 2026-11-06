import Langlands.Geometry.Building.AffineRootSystem
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-! # Maps that are distance-nonincreasing on closed facets

For a locally finite family of affine functionals on a finite-dimensional real
normed affine space, a map which does not increase distances between two
points of any closed facet does not increase any distance. This is the
segment-subdivision step in the proof of KP Proposition 4.2.2(3).
-/

noncomputable section

open Filter Topology Set

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- A real number closer to `v` than `|v|` has the sign of `v`. -/
theorem sign_eq_of_abs_sub_lt {u v : ℝ} (h : |u - v| < |v|) :
    SignType.sign u = SignType.sign v := by
  rcases lt_trichotomy v 0 with hv | hv | hv
  · rw [abs_of_neg hv] at h
    have hu : u < 0 := by linarith [le_abs_self (u - v)]
    rw [sign_neg hu, sign_neg hv]
  · subst hv
    simp at h
    exact absurd h (not_lt.2 (abs_nonneg u))
  · rw [abs_of_pos hv] at h
    have hu : 0 < u := by linarith [neg_abs_le (u - v)]
    rw [sign_pos hu, sign_pos hv]

/-- The value of an affine functional moves by at most the operator norm of
its linear part times the distance. -/
theorem abs_apply_sub_apply_le (ψ : P →ᵃ[ℝ] ℝ) (x y : P) :
    |ψ y - ψ x| ≤ ‖LinearMap.toContinuousLinearMap ψ.linear‖ * dist y x := by
  rw [dist_eq_norm_vsub V y x, ← vsub_eq_sub, ← AffineMap.linearMap_vsub, ← Real.norm_eq_abs,
    ← LinearMap.coe_toContinuousLinearMap' ψ.linear]
  exact ContinuousLinearMap.le_opNorm _ _

/-- Local finiteness: every point `x` lies in the closed facet of every
sufficiently near point. -/
theorem eventually_mem_facetClosure {Ψ : Set (P →ᵃ[ℝ] ℝ)}
    (hΨ : ∀ (x : P) (bound : Module.Dual ℝ V → ℝ),
      {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ bound ψ.linear}.Finite) (x : P) :
    ∀ᶠ y in 𝓝 x, x ∈ facetClosure Ψ y := by
  set S := {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ ‖LinearMap.toContinuousLinearMap ψ.linear‖}
  have hS : S.Finite := hΨ x fun a => ‖LinearMap.toContinuousLinearMap a‖
  have hnear : ∀ ψ ∈ S, ∀ᶠ y in 𝓝 x, ψ x = 0 ∨ |ψ y - ψ x| < |ψ x| := by
    intro ψ _
    by_cases hψ : ψ x = 0
    · exact Eventually.of_forall fun _ => Or.inl hψ
    · have hcont := (ψ.continuous_of_finiteDimensional.tendsto x).eventually
        (Metric.ball_mem_nhds (ψ x) (abs_pos.2 hψ))
      exact hcont.mono fun y hy => Or.inr (by simpa [Real.dist_eq] using hy)
  have hfar : ∀ᶠ y in 𝓝 x, dist y x < 1 := Metric.ball_mem_nhds x one_pos
  filter_upwards [hS.eventually_all.2 hnear, hfar] with y hy hyx
  intro ψ hψ
  have hlt : ψ x = 0 ∨ |ψ y - ψ x| < |ψ x| := by
    by_cases hψS : ψ ∈ S
    · exact hy ψ hψS
    · right
      have hbig : ‖LinearMap.toContinuousLinearMap ψ.linear‖ < |ψ x| :=
        lt_of_not_ge fun h => hψS ⟨hψ, h⟩
      calc |ψ y - ψ x| ≤ ‖LinearMap.toContinuousLinearMap ψ.linear‖ * dist y x :=
            abs_apply_sub_apply_le ψ x y
        _ ≤ ‖LinearMap.toContinuousLinearMap ψ.linear‖ * 1 :=
            mul_le_mul_of_nonneg_left hyx.le (norm_nonneg _)
        _ < |ψ x| := by rwa [mul_one]
  rcases hlt with h0 | hlt
  · left
    rw [h0, sign_zero]
  · right
    exact (sign_eq_of_abs_sub_lt hlt).symm

/-- KP Proposition 4.2.2(3), segment-subdivision step: if `f` does not
increase the distance between any two points of a common closed facet, then
`f` does not increase distances. -/
theorem dist_le_of_forall_mem_facetClosure {Q : Type*} [PseudoMetricSpace Q]
    {Ψ : Set (P →ᵃ[ℝ] ℝ)}
    (hΨ : ∀ (x : P) (bound : Module.Dual ℝ V → ℝ),
      {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ bound ψ.linear}.Finite)
    {f : P → Q}
    (hf : ∀ p u v, u ∈ facetClosure Ψ p → v ∈ facetClosure Ψ p →
      dist (f u) (f v) ≤ dist u v)
    (a b : P) : dist (f a) (f b) ≤ dist a b := by
  set γ : ℝ → P := fun t => AffineMap.lineMap a b t
  have hγ : Continuous γ := AffineMap.lineMap_continuous
  set L := dist a b
  have hloc : ∀ t, ∀ᶠ s in 𝓝 t, dist (f (γ t)) (f (γ s)) ≤ dist t s * L := by
    intro t
    filter_upwards [hγ.continuousAt.eventually (eventually_mem_facetClosure hΨ (γ t))]
      with s hs
    calc dist (f (γ t)) (f (γ s)) ≤ dist (γ t) (γ s) :=
          hf (γ s) (γ t) (γ s) hs (mem_facetClosure_self Ψ (γ s))
      _ = dist t s * L := dist_lineMap_lineMap a b t s
  have hcont : Continuous fun t => f (γ t) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hg : Tendsto (fun s => dist s t * L) (𝓝 t) (𝓝 0) := by
      have h := ((continuous_id.dist (continuous_const (y := t))).tendsto t).mul_const L
      simpa using h
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
      fun _ => dist_nonneg) ((hloc t).mono fun s hs => ?_) hg)
    rw [dist_comm (f (γ s)), dist_comm s]
    exact hs
  set S := {t : ℝ | dist (f a) (f (γ t)) ≤ t * L}
  have hS : IsClosed (S ∩ Icc 0 1) :=
    (isClosed_le (continuous_const.dist hcont) (continuous_id.mul continuous_const)).inter
      isClosed_Icc
  have h0 : (0 : ℝ) ∈ S := by
    simp [S, γ]
  have hstep : ∀ t ∈ S ∩ Ico 0 1, S ∈ 𝓝[>] t := by
    rintro t ⟨ht, -⟩
    filter_upwards [nhdsWithin_le_nhds (hloc t), self_mem_nhdsWithin] with s hs hts
    change dist (f a) (f (γ s)) ≤ s * L
    have hts' : dist t s = s - t := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hts)]
    calc dist (f a) (f (γ s)) ≤ dist (f a) (f (γ t)) + dist (f (γ t)) (f (γ s)) :=
          dist_triangle _ _ _
      _ ≤ t * L + (s - t) * L := add_le_add ht (hts' ▸ hs)
      _ = s * L := by ring
  have h1 : (1 : ℝ) ∈ S := hS.Icc_subset_of_forall_mem_nhdsWithin h0 hstep ⟨zero_le_one, le_rfl⟩
  simpa [S, γ, L] using h1

end Langlands.Geometry.Building.AffineRootSystem
