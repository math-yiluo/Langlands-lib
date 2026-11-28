import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialChart
import Mathlib.Topology.MetricSpace.Contracting

/-! # Uniform small exponential charts for closed subalgebras -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Metric Function Filter _root_.Topology
open scoped NNReal

variable {F A : Type*} [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A]

omit [IsUltrametricDist F] [IsUltrametricDist A] [CompleteSpace A] in
/-- A closed algebra embedding commutes with the exponential, by transport of
convergent and divergent series along the closed embedding. -/
theorem map_exp_sub_one_of_closedEmbedding {B : Type*} [NormedRing B] [NormedAlgebra F B]
    (j : B →ₐ[F] A) (hj : IsClosedEmbedding j) (x : B) :
    j (NormedSpace.exp x - 1) = NormedSpace.exp (j x) - 1 := by
  rw [map_sub, map_one]
  congr 1
  rw [congrFun (NormedSpace.exp_eq_tsum F (𝔸 := B)) x,
    congrFun (NormedSpace.exp_eq_tsum F (𝔸 := A)) (j x)]
  rw [hj.map_tsum (g := j)]
  exact tsum_congr fun n => by rw [map_smul, map_pow]

/-- One radius works in the ambient algebra and in all its closed subalgebras.
On the corresponding balls, `exp − 1` gives an isometric self-bijection. -/
def SmallExponentialSubalgebraStatement (F A : Type*) [NontriviallyNormedField F] [CharZero F]
    [IsUltrametricDist F] [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A] : Prop :=
  ∃ ε > (0 : ℝ), ∀ r : ℝ, 0 < r → r ≤ ε →
    closedBall (0 : A) r ⊆ eball 0 (NormedSpace.expSeries F A).radius ∧
      ∀ S : Subalgebra F A, IsClosed (S : Set A) →
        ∃ e : (closedBall (0 : A) r ∩ (S : Set A) : Set A) ≃ᵢ
            (closedBall (0 : A) r ∩ (S : Set A) : Set A),
          ∀ x, (e x : A) = NormedSpace.exp (x : A) - 1

set_option maxHeartbeats 1200000 in
theorem smallExponentialSubalgebra : SmallExponentialSubalgebraStatement F A := by
  let f (x : A) := NormedSpace.exp x - 1
  let u (x : A) := f x - x
  have hf₀ : f 0 = 0 := by simp [f]
  have hu₀ : u 0 = 0 := by simp only [u, hf₀, sub_zero]
  let d : A ≃L[F] A := ContinuousLinearEquiv.refl F A
  have hradius := exponentialPositiveRadius F A
  have hd : HasStrictFDerivAt f d.toContinuousLinearMap 0 :=
    (hasStrictFDerivAt_exp_zero_of_radius_pos hradius).sub_const 1
  obtain ⟨U, hU, hApprox⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  let c : ℝ≥0 := 1 / 2
  have hc : (c : ℝ) < 1 := by norm_num [c]
  have hLip : LipschitzOnWith c u U := hApprox.lipschitzOnWith
  have hNear : U ∩ eball (0 : A) (NormedSpace.expSeries F A).radius ∈ 𝓝 (0 : A) :=
    inter_mem hU (eball_mem_nhds _ (by simpa [ExponentialPositiveRadiusStatement] using hradius))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hNear
  refine ⟨ε / 2, half_pos hε, fun r hr hrε => ?_⟩
  have hball : closedBall (0 : A) r ⊆ U ∩ eball (0 : A) (NormedSpace.expSeries F A).radius :=
    (closedBall_subset_ball (hrε.trans_lt (half_lt_self hε))).trans hεU
  refine ⟨fun x hx => (hball hx).2, fun S hS => ?_⟩
  let C := closedBall (0 : A) r ∩ (S : Set A)
  have h0 : (0 : A) ∈ C := ⟨mem_closedBall_self hr.le, S.zero_mem⟩
  have hfS (x : A) (hx : x ∈ C) : f x ∈ S := by
    have hj : IsClosedEmbedding (S.val : S → A) :=
      ⟨IsEmbedding.subtypeVal, by
        change IsClosed (range (Subtype.val : S → A))
        rwa [Subtype.range_coe]⟩
    let w : S := ⟨x, hx.2⟩
    have hw := map_exp_sub_one_of_closedEmbedding S.val hj w
    change S.val (NormedSpace.exp w - 1) = f x at hw
    exact hw ▸ (NormedSpace.exp w - 1).property
  have huNorm {x : A} (hx : x ∈ C) : ‖u x‖ ≤ r := by
    have h := hLip.dist_le_mul x (hball hx.1).1 0 (hball h0.1).1
    rw [hu₀, dist_zero_right, dist_zero_right] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) hc.le).trans (dist_zero_right x ▸ hx.1))
  have huS (x : A) (hx : x ∈ C) : u x ∈ S := S.sub_mem (hfS x hx) hx.2
  have hdist {x y : A} (hx : x ∈ C) (hy : y ∈ C) : dist (f x) (f y) = dist x y := by
    by_cases hxy : x = y
    · simp [hxy]
    have hle := hLip.dist_le_mul x (hball hx.1).1 y (hball hy.1).1
    rw [dist_eq_norm, dist_eq_norm] at hle
    have hlt := hle.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) hc)
    have hsum : f x - f y = (u x - u y) + (x - y) := by dsimp only [u]; abel
    rw [dist_eq_norm, dist_eq_norm, hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne,
      max_eq_right hlt.le]
  have hfC : MapsTo f C C := by
    intro x hx
    refine ⟨?_, hfS x hx⟩
    rw [mem_closedBall, ← hf₀, hdist hx h0]
    exact hx.1
  let g : C → C := hfC.restrict f C C
  have hIso : Isometry g := Isometry.of_dist_eq fun x y => hdist x.property y.property
  have hSurj : Surjective g := by
    intro y
    let v (x : A) := y.val - u x
    have hv : MapsTo v C C := by
      intro x hx
      refine ⟨?_, S.sub_mem y.property.2 (huS x hx)⟩
      rw [mem_closedBall, dist_zero_right]
      change ‖y.val - u x‖ ≤ r
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (dist_zero_right (y : A) ▸ y.property.1) ((norm_neg _).trans_le (huNorm hx)))
    have hvCon : ContractingWith c (hv.restrict v C C) := by
      refine ⟨by exact_mod_cast hc, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
      change dist (y.val - u x.val) (y.val - u z.val) ≤ (c : ℝ) * dist x.val z.val
      rw [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev, ← dist_eq_norm]
      exact hLip.dist_le_mul _ (hball x.property.1).1 _ (hball z.property.1).1
    obtain ⟨x, hx, hFixed, _⟩ := hvCon.exists_fixedPoint' (isClosed_closedBall.inter hS).isComplete hv
      h0 (edist_ne_top _ _)
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change f x = y.val
    change y.val - (f x - x) = x at hFixed
    calc
      f x = x + (f x - x) := by abel
      _ = y.val := (eq_add_of_sub_eq hFixed).symm
  exact ⟨{ Equiv.ofBijective g ⟨hIso.injective, hSurj⟩ with isometry_toFun := hIso }, fun _ => rfl⟩

end Langlands.HarmonicAnalysis.UnitConjugation
