import Langlands.HarmonicAnalysis.UltrametricBallPushforward

/-! # Change of variables on one ultrametric ball

Let `X` be a proper ultrametric normed additive group with an additive Haar measure `ν`, `A` a
homeomorphism of `X` with `A 0 = 0` and `ν.map A = c • ν`, and `χ : X → X` with `χ 0 = 0` such
that `u(x) = A⁻¹(χ x) − x` is continuous and has Lipschitz constant `< 1` on the closed ball
`B(0, r)`, so that `χ = A ∘ (id + u)`. Then `χ` sends `ν` restricted to the ball to `c` times `ν`
restricted to the image of the ball under `A`. See the paired Markdown.
-/

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {X : Type*} [NormedAddCommGroup X] [IsUltrametricDist X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **One-ball change of variables.** -/
theorem map_restrict_closedBall_of_perturbation (ν : Measure X) [ν.IsAddHaarMeasure]
    (A : X ≃ₜ X) (c : ℝ≥0∞) (hA : ν.map A = c • ν) (χ : X → X)
    (hcont : Continuous fun x => A.symm (χ x) - x) {r : ℝ} (hr : 0 ≤ r) {k : ℝ≥0} (hk : k < 1)
    (hu : LipschitzOnWith k (fun x => A.symm (χ x) - x) (closedBall 0 r)) (h0 : χ 0 = 0)
    (hA0 : A 0 = 0) :
    (ν.restrict (closedBall 0 r)).map χ = c • ν.restrict (A '' closedBall 0 r) := by
  let u : X → X := fun x => A.symm (χ x) - x
  have hχ : χ = A ∘ (fun x => x + u x) := by
    funext x
    simp [u]
  have hu0 : u 0 = 0 := by
    have : A.symm 0 = 0 := by rw [A.symm_apply_eq]; exact hA0.symm
    simp [u, h0, this]
  have hpert := HarmonicAnalysis.map_closedBall_add_perturbation ν (0 : X) hr hu hk hcont
  change Measure.map (fun x => x + u x) _ = ν.restrict (closedBall (0 + u 0) r) at hpert
  rw [hu0, add_zero] at hpert
  have hm : Measurable (fun x => x + u x) := (continuous_id.add hcont).measurable
  rw [hχ, ← Measure.map_map A.continuous.measurable hm, hpert]
  have hemb : MeasurableEmbedding A := A.isClosedEmbedding.measurableEmbedding
  have key : (ν.restrict (closedBall 0 r)).map A = (ν.map A).restrict (A '' closedBall 0 r) := by
    rw [hemb.restrict_map, A.injective.preimage_image]
  rw [key, hA, Measure.restrict_smul]

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- In a complete ultrametric normed group, a perturbation `u` with `u 0 = 0` and Lipschitz
constant `< 1` on the closed ball `B(0, r)` makes `id + u` map that ball onto itself. -/
theorem image_closedBall_add_perturbation' [CompleteSpace X] {r : ℝ} (hr : 0 ≤ r) {u : X → X}
    {c : ℝ≥0} (hu : LipschitzOnWith c u (closedBall 0 r)) (hc : c < 1) (hu0 : u 0 = 0) :
    (fun x => x + u x) '' closedBall 0 r = closedBall 0 r := by
  have h0 : (0 : X) ∈ closedBall 0 r := mem_closedBall_self hr
  have hdist : ∀ x ∈ closedBall (0 : X) r, ‖x + u x‖ ≤ ‖x‖ := by
    intro x hx
    have hux : ‖u x‖ ≤ ‖x‖ := by
      have := hu.dist_le_mul x hx 0 h0
      rw [hu0, dist_zero_right, dist_zero_right] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast hc.le))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl hux)
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact (hdist x (mem_closedBall_zero_iff.mpr hx)).trans hx
  intro b hb
  let t : X → X := fun x => b - u x
  have ht : LipschitzOnWith c t (closedBall 0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have he : t x - t y = -(u x - u y) := by
      simp only [t]
      abel
    rw [dist_eq_norm, he, norm_neg, ← dist_eq_norm]
    exact hu.dist_le_mul x hx y hy
  have hmaps : MapsTo t (closedBall 0 r) (closedBall 0 r) := by
    intro x hx
    have hbound : ‖u x‖ ≤ r := by
      have := hu.dist_le_mul x hx 0 h0
      rw [hu0, dist_zero_right, dist_zero_right] at this
      exact this.trans ((mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast hc.le)).trans
        (mem_closedBall_zero_iff.mp hx))
    rw [mem_closedBall_zero_iff]
    change ‖b - u x‖ ≤ r
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (mem_closedBall_zero_iff.mp hb) (by rwa [norm_neg]))
  obtain ⟨x, hx, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    (K := c) (f := t) isClosed_closedBall.isComplete hmaps
    ⟨hc, ht.to_restrict⟩ h0 (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  have hfix' : b - u x = x := hfix
  exact (sub_eq_iff_eq_add.mp hfix').symm

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The image of the ball under the chart in the one-ball change of variables. -/
theorem image_closedBall_of_perturbation [CompleteSpace X] (A : X ≃ₜ X) (χ : X → X) {r : ℝ}
    (hr : 0 ≤ r) {k : ℝ≥0} (hk : k < 1)
    (hu : LipschitzOnWith k (fun x => A.symm (χ x) - x) (closedBall 0 r)) (h0 : χ 0 = 0)
    (hA0 : A 0 = 0) :
    χ '' closedBall 0 r = A '' closedBall 0 r := by
  have hu0 : A.symm (χ 0) - 0 = 0 := by
    have : A.symm 0 = 0 := by rw [A.symm_apply_eq]; exact hA0.symm
    simp [h0, this]
  have himg := image_closedBall_add_perturbation' hr hu hk hu0
  have hχ : χ = A ∘ (fun x => x + (A.symm (χ x) - x)) := by
    funext x
    simp
  rw [hχ, image_comp, himg]

/-- **One-ball change of variables**, for a topology given separately and equal to the norm
topology. -/
theorem map_restrict_closedBall_of_perturbation' {Y : Type*} [NormedAddCommGroup Y]
    [IsUltrametricDist Y] [ProperSpace Y] [t : TopologicalSpace Y]
    (ht : t = PseudoMetricSpace.toUniformSpace.toTopologicalSpace) [MeasurableSpace Y]
    [BorelSpace Y] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (A : Y ≃ₜ Y) (c : ℝ≥0∞) (hA : ν.map A = c • ν) (χ : Y → Y)
    (hcont : Continuous fun x => A.symm (χ x) - x) {r : ℝ} (hr : 0 ≤ r) {k : ℝ≥0} (hk : k < 1)
    (hu : LipschitzOnWith k (fun x => A.symm (χ x) - x) (closedBall 0 r)) (h0 : χ 0 = 0)
    (hA0 : A 0 = 0) :
    (ν.restrict (closedBall 0 r)).map χ = c • ν.restrict (A '' closedBall 0 r) := by
  subst ht
  exact map_restrict_closedBall_of_perturbation ν A c hA χ hcont hr hk hu h0 hA0

/-- The image of the ball under the chart, for a topology given separately and equal to the norm
topology. -/
theorem image_closedBall_of_perturbation'' {Y : Type*} [NormedAddCommGroup Y]
    [IsUltrametricDist Y] [ProperSpace Y] [t : TopologicalSpace Y]
    (ht : t = PseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (A : Y ≃ₜ Y) (χ : Y → Y) {r : ℝ} (hr : 0 ≤ r) {k : ℝ≥0} (hk : k < 1)
    (hu : LipschitzOnWith k (fun x => A.symm (χ x) - x) (closedBall 0 r)) (h0 : χ 0 = 0)
    (hA0 : A 0 = 0) :
    χ '' closedBall 0 r = A '' closedBall 0 r := by
  subst ht
  have : CompleteSpace Y := complete_of_proper
  exact image_closedBall_of_perturbation A χ hr hk hu h0 hA0

end Langlands.BaseChange.TwistedLocalDescent
