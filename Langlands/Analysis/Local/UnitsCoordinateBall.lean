import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Compact open groups of units from ultrametric coordinates -/

noncomputable section

open Filter Metric Set Topology

namespace Langlands.Analysis

universe u v w

variable {K : Type u} {R : Type v} {V : Type w}
  [NontriviallyNormedField K] [NormedRing R] [NormedAlgebra K R] [HasSummableGeomSeries R]
  [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V] [ProperSpace V]

/-- In linear coordinates on a normed algebra, every sufficiently small
positive-radius closed ball at zero is the translated image of a compact
open subgroup of units. -/
abbrev UnitsCoordinateBallStatement : Prop :=
  ∀ {K : Type u} {R : Type v} {V : Type w}
    [NontriviallyNormedField K] [NormedRing R] [NormedAlgebra K R] [HasSummableGeomSeries R]
    [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V] [ProperSpace V]
    (e : R ≃L[K] V),
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioc 0 r₀, ∃ U : OpenSubgroup Rˣ,
      IsCompact (U : Set Rˣ) ∧
      (U : Set Rˣ) = {g | e (g.val - 1) ∈ closedBall (0 : V) r} ∧
      Set.range (fun g : U => e ((g : Rˣ).val - 1)) = closedBall (0 : V) r

theorem unitsCoordinateBall : UnitsCoordinateBallStatement.{u, v, w} := by
  intro K R V _ _ _ _ _ _ _ _ e
  let C := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ *
    ‖e.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmul (x y : R) : ‖e (x * y)‖ ≤ C * ‖e x‖ * ‖e y‖ := by
    have hx := e.symm.toContinuousLinearMap.le_opNorm (e x)
    have hy := e.symm.toContinuousLinearMap.le_opNorm (e y)
    change ‖e.symm (e x)‖ ≤ _ at hx
    change ‖e.symm (e y)‖ ≤ _ at hy
    rw [e.symm_apply_apply] at hx hy
    calc
      ‖e (x * y)‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x * y‖ :=
        e.toContinuousLinearMap.le_opNorm (x * y)
      _ ≤ ‖e.toContinuousLinearMap‖ * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le x y) (norm_nonneg _)
      _ ≤ ‖e.toContinuousLinearMap‖ *
          ((‖e.symm.toContinuousLinearMap‖ * ‖e x‖) *
            (‖e.symm.toContinuousLinearMap‖ * ‖e y‖)) := by
        gcongr
      _ = C * ‖e x‖ * ‖e y‖ := by dsimp [C]; ring
  have hu : {v : V | IsUnit (1 + e.symm v)} ∈ 𝓝 (0 : V) :=
    (Units.isOpen.preimage (continuous_const.add e.symm.continuous)).mem_nhds
      (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  let r₀ := min (ε / 2) (1 / (C + 1))
  have hCp : 0 < C + 1 := by positivity
  refine ⟨r₀, lt_min (by positivity) (by positivity), fun r hr => ?_⟩
  have hCr : C * r < 1 := calc
    C * r ≤ C * (1 / (C + 1)) :=
      mul_le_mul_of_nonneg_left (hr.2.trans (min_le_right _ _)) hC
    _ = C / (C + 1) := by rw [mul_one_div]
    _ < 1 := (div_lt_one hCp).mpr (by linarith)
  have hunit (v : V) (hv : v ∈ closedBall (0 : V) r) : IsUnit (1 + e.symm v) :=
    hεu (Metric.closedBall_subset_ball
      ((hr.2.trans (min_le_left _ _)).trans_lt (by linarith)) hv)
  let U : OpenSubgroup Rˣ :=
    { carrier := {g | e (g.val - 1) ∈ closedBall (0 : V) r}
      isOpen' := (IsUltrametricDist.isOpen_closedBall _ hr.1.ne').preimage
        (e.continuous.comp (Units.continuous_val.sub continuous_const))
      one_mem' := by change e ((1 : R) - 1) ∈ closedBall _ _; simp [hr.1.le]
      mul_mem' := by
        intro g h hg hh
        let x := g.val - 1
        let y := h.val - 1
        change e x ∈ closedBall (0 : V) r at hg
        change e y ∈ closedBall (0 : V) r at hh
        have hx : ‖e x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hg
        have hy : ‖e y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hh
        have hxy : ‖e (x * y)‖ ≤ r :=
          (hmul x y).trans ((mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hx hC) (norm_nonneg _)).trans
                ((mul_le_mul_of_nonneg_right hCr.le (norm_nonneg _)).trans (by simpa using hy)))
        have heq : (g * h).val - 1 = (x + y) + x * y := by
          change g.val * h.val - 1 = _
          dsimp [x, y]
          noncomm_ring
        change e ((g * h).val - 1) ∈ closedBall (0 : V) r
        rw [Metric.mem_closedBall, dist_zero_right, heq, e.map_add, e.map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans <|
          max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)) hxy
      inv_mem' := by
        intro g hg
        let x := g.val - 1
        let y := (g⁻¹ : Rˣ).val - 1
        change e x ∈ closedBall (0 : V) r at hg
        have hx : ‖e x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hg
        have heq : y = -(x + x * y) := by
          have hgg : g.val * (g⁻¹ : Rˣ).val = 1 := congrArg Units.val (mul_inv_cancel g)
          dsimp [x, y]
          rw [mul_sub, sub_mul, one_mul, mul_one, hgg]
          abel
        change e y ∈ closedBall (0 : V) r
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra! hy
        have hnorm : ‖e y‖ ≤ max ‖e x‖ ‖e (x * y)‖ := by
          conv_lhs => rw [heq, e.map_neg, norm_neg, e.map_add]
          exact IsUltrametricDist.norm_add_le_max _ _
        have hxy : ‖e (x * y)‖ < ‖e y‖ := calc
          ‖e (x * y)‖ ≤ C * ‖e x‖ * ‖e y‖ := hmul x y
          _ ≤ C * r * ‖e y‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hC) (norm_nonneg _)
          _ < ‖e y‖ := by
            simpa only [one_mul] using mul_lt_mul_of_pos_right hCr (hr.1.trans hy)
        exact (not_lt_of_ge hnorm) (max_lt (hx.trans_lt hy) hxy) }
  let f : Rˣ → V := fun g => e (g.val - 1)
  have hf : IsOpenEmbedding f :=
    e.toHomeomorph.isOpenEmbedding.comp
      ((Homeomorph.subRight (1 : R)).isOpenEmbedding.comp Units.isOpenEmbedding_val)
  have hrange : Set.range (fun g : U => f g.val) = closedBall (0 : V) r := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      exact g.property
    · intro hv
      let g := (hunit v hv).unit
      have hg : f g = v := by
        change e (g.val - 1) = v
        rw [(hunit v hv).unit_spec, add_sub_cancel_left, e.apply_symm_apply]
      exact ⟨⟨g, by show f g ∈ closedBall (0 : V) r; rw [hg]; exact hv⟩, hg⟩
  have himage : f '' (U : Set Rˣ) = closedBall (0 : V) r :=
    (Set.range_domRestrict f (U : Set Rˣ)).symm.trans hrange
  exact ⟨U, hf.isEmbedding.isCompact_iff.mpr (himage ▸ isCompact_closedBall _ _), rfl, hrange⟩

end Langlands.Analysis
