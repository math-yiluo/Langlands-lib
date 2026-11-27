import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialChart
import Langlands.HarmonicAnalysis.UltrametricBallPushforward
import Mathlib.Topology.Algebra.Indicator

/-! # The exponential in small ultrametric balls -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Metric Filter Set Function
open scoped NNReal _root_.Topology

/-- On all sufficiently small positive-radius closed balls at zero, `exp − 1`
is an isometric self-bijection preserving restricted additive Haar measure. -/
def ExponentialBallTransportStatement (F A : Type*) [NontriviallyNormedField F] [CharZero F]
    [IsUltrametricDist F] [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A]
    [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] : Prop :=
  ∃ ε > (0 : ℝ), ∀ r : ℝ, 0 < r → r ≤ ε →
    ∃ e : closedBall (0 : A) r ≃ᵢ closedBall (0 : A) r,
      (∀ x, (e x : A) = NormedSpace.exp (x : A) - 1) ∧
      ∀ [ProperSpace A] (μ : Measure A) [μ.IsAddHaarMeasure],
        Measure.map (fun x : A => NormedSpace.exp x - 1) (μ.restrict (closedBall 0 r)) =
          μ.restrict (closedBall 0 r)

variable {F A : Type*} [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem exponentialBallTransport : ExponentialBallTransportStatement F A := by
  let f (x : A) := NormedSpace.exp x - 1
  have hf₀ : f 0 = 0 := by simp [f]
  let d : A ≃L[F] A := ContinuousLinearEquiv.refl F A
  have hd : HasStrictFDerivAt f d.toContinuousLinearMap 0 :=
    (hasStrictFDerivAt_exp_zero_of_radius_pos (exponentialPositiveRadius F A)).sub_const 1
  obtain ⟨U, hU, hApprox⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  have hL : LipschitzOnWith (1 / 2 : ℝ≥0) (fun x => f x - x) U :=
    hApprox.lipschitzOnWith
  have hdist {x y : A} (hx : x ∈ U) (hy : y ∈ U) : dist (f x) (f y) = dist x y := by
    by_cases hxy : x = y
    · simp [hxy]
    have hlt : ‖f x - f y - (x - y)‖ < ‖x - y‖ := calc
      _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by simpa [d] using hApprox x hx y hy
      _ < _ := by have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hxy); linarith
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [sub_add_cancel, max_eq_right hlt.le] using
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp hU
  let e₀ := hd.toOpenPartialHomeomorph f
  let e₁ := e₀.restrOpen (ball 0 a) isOpen_ball
  have h0s : 0 ∈ e₁.source := ⟨hd.mem_toOpenPartialHomeomorph_source, mem_ball_self ha⟩
  have h0t : 0 ∈ e₁.target := hf₀ ▸ e₁.map_source h0s
  have heU : e₁.source ⊆ U := fun _ hx => haU hx.2
  have hb : e₁.source ∩ e₁.target ∈ 𝓝 (0 : A) :=
    (e₁.open_source.inter e₁.open_target).mem_nhds ⟨h0s, h0t⟩
  obtain ⟨b, hb0, hbsub⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨b / 2, half_pos hb0, fun r hr hrb => ?_⟩
  let S := closedBall (0 : A) r
  have hS : S ⊆ e₁.source ∩ e₁.target := fun _ hx => hbsub
    (closedBall_subset_ball (hrb.trans_lt (half_lt_self hb0)) hx)
  have hmap : MapsTo f S S := by
    intro x hx
    change dist (f x) 0 ≤ r
    rw [← hf₀, hdist (heU (hS hx).1) (mem_of_mem_nhds hU)]
    exact hx
  have hmapInv : MapsTo e₁.symm S S := by
    intro y hy
    have ht := (hS hy).2
    have hx := e₁.map_target ht
    have heq : f (e₁.symm y) = y := e₁.right_inv ht
    change dist (e₁.symm y) 0 ≤ r
    rw [← hdist (heU hx) (mem_of_mem_nhds hU), hf₀, heq]
    exact hy
  let e : S ≃ᵢ S :=
    { toFun := fun x => ⟨f x, hmap x.property⟩
      invFun := fun y => ⟨e₁.symm y, hmapInv y.property⟩
      left_inv := fun x => Subtype.ext (e₁.left_inv (hS x.property).1)
      right_inv := fun y => Subtype.ext (e₁.right_inv (hS y.property).2)
      isometry_toFun := Isometry.of_dist_eq fun x y => hdist (heU (hS x.property).1) (heU (hS y.property).1) }
  refine ⟨e, fun _ => rfl, ?_⟩
  intro _ μ _
  let u := S.indicator (fun x => f x - x)
  have hSu : LipschitzOnWith (1 / 2 : ℝ≥0) u S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [u, indicator_of_mem hx, indicator_of_mem hy]
    exact hL.dist_le_mul x (heU (hS hx).1) y (heU (hS hy).1)
  have hCl : IsClopen S := IsUltrametricDist.isClopen_closedBall _ hr.ne'
  have huc : Continuous u := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply ContinuousOn.continuousAt_indicator
    · exact hL.continuousOn.mono (interior_subset.trans (fun _ hx => heU (hS hx).1))
    · rw [isClopen_iff_frontier_eq_empty.mp hCl]
      exact notMem_empty x
  have hu₀ : u 0 = 0 := by simp [u, S, mem_closedBall_self hr.le, hf₀]
  have hae : f =ᵐ[μ.restrict S] fun x => x + u x := by
    filter_upwards [ae_restrict_mem hCl.2.measurableSet] with x hx
    dsimp only [u]
    rw [indicator_of_mem hx]
    abel
  change Measure.map f (μ.restrict S) = _
  rw [Measure.map_congr hae]
  simpa only [hu₀, add_zero] using
    (map_closedBall_add_perturbation μ (0 : A) hr.le hSu (by norm_num) huc)

end Langlands.HarmonicAnalysis.UnitConjugation
