import Langlands.Representation.Archimedean.CompactSmoothAverage
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Compact approximation in the genuine word-derivative topology -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Manifold ContDiff

namespace Langlands.Archimedean.CompactSmoothAverage

universe u𝔤 uG uH uN uE uX

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
  [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold 𝓘(ℝ, H) ∞ N]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) {v : N → E}
  (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
    (fun p : G × N => π p.1 (v p.2)))

/-- The original family, valued in its genuine word-derivative topology. -/
def derivativeFamily (n : N) : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π :=
  (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).symm
    ⟨v n, isSmoothVector_family π hv n⟩

omit [IsManifold 𝓘(ℝ, H) ∞ N] in
@[simp]
theorem derivativeCoordinates_derivativeFamily (n : N) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π
      (derivativeFamily π hv n) Xs =
        iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v n) := by
  simp only [DerivativeSmoothVectors.derivativeCoordinates_apply, derivativeFamily,
    LinearEquiv.apply_symm_apply]

theorem continuous_derivativeFamily' : Continuous (derivativeFamily π hv) :=
  continuous_derivativeFamily π hv

variable [FiniteDimensional ℝ 𝔤] [CompleteSpace E]
  {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Only the nonzero part of a normalized weight must be close to the target
parameter; values outside its support do not contribute to the estimate. -/
theorem norm_integral_average_sub_le_of_support
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (a : C(X, ℂ)) (F : C(X, B)) (b : B) {ε : ℝ}
    (ha : (∫ x, a x ∂μ) = 1) (hnorm : (∫ x, ‖a x‖ ∂μ) = 1)
    (hF : ∀ x, a x ≠ 0 → ‖F x - b‖ ≤ ε) :
    ‖(∫ x, a x • F x ∂μ) - b‖ ≤ ε := by
  have h1 : Integrable (fun x => a x • F x) μ :=
    (a.continuous.smul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun x => a x • b) μ :=
    (a.continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ x, a x • F x ∂μ) - b = ∫ x, a x • (F x - b) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, ha, one_smul]
  rw [heq]
  have hb : Integrable (fun x => ‖a x‖ * ε) μ :=
    (a.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ‖∫ x, a x • (F x - b) ∂μ‖ ≤ ∫ x, ‖a x‖ * ε ∂μ :=
      norm_integral_le_of_norm_le hb (Eventually.of_forall fun x => by
        by_cases hx : a x = 0
        · simp [hx]
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hF x hx) (norm_nonneg _))
    _ = ε := by rw [integral_mul_const, hnorm, one_mul]

/-- A neighborhood of one family member controls every normalized average whose
nonzero weight is supported over that neighborhood. All genuine derivative
words in the given smooth-vector neighborhood are controlled simultaneously. -/
theorem exists_average_neighborhood (n₀ : N)
    (V : Set (DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π))
    (hV : V ∈ 𝓝 (derivativeFamily π hv n₀)) :
    ∃ U : Set N, U ∈ 𝓝 n₀ ∧
      ∀ (a : C(X, ℂ)) (j : C(X, N)),
        (∀ x, a x ≠ 0 → j x ∈ U) →
        (∫ x, a x ∂μ) = 1 → (∫ x, ‖a x‖ ∂μ) = 1 →
        weightAverageLM π μ j hv a ∈ V := by
  classical
  rw [(DerivativeSmoothVectors.isEmbedding_derivativeCoordinates 𝓘(ℝ, 𝔤) π).isInducing.nhds_eq_comap]
    at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hW
  choose ε hε hball using fun i : I => Metric.mem_nhds_iff.mp (ht i)
  let U : Set N := ⋂ i : I,
    (fun n => iteratedLieDerivative 𝓘(ℝ, 𝔤) π i.val (v n)) ⁻¹'
      ball (iteratedLieDerivative 𝓘(ℝ, 𝔤) π i.val (v n₀)) (ε i / 2)
  refine ⟨U, ?_, ?_⟩
  · apply Filter.iInter_mem.mpr
    intro i
    exact (continuous_iteratedLieDerivative_family π hv i.val).continuousAt
      (ball_mem_nhds _ (half_pos (hε i)))
  · intro a j hj ha hnorm
    apply hWV
    apply hsub
    intro i hi
    let k : I := ⟨i, hi⟩
    apply hball k
    rw [mem_ball, dist_eq_norm]
    have hb : ‖DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π
        (weightAverageLM π μ j hv a) i -
        iteratedLieDerivative 𝓘(ℝ, 𝔤) π i (v n₀)‖ ≤ ε k / 2 := by
      rw [derivativeCoordinates_weightAverageLM]
      let F : C(X, E) :=
        ⟨fun x => iteratedLieDerivative 𝓘(ℝ, 𝔤) π i (v (j x)),
          (continuous_iteratedLieDerivative_family π hv i).comp j.continuous⟩
      apply norm_integral_average_sub_le_of_support μ a F
        (iteratedLieDerivative 𝓘(ℝ, 𝔤) π i (v n₀)) ha hnorm
      intro x hx
      simpa only [F, k, ContinuousMap.coe_mk, dist_eq_norm] using
        (mem_ball.mp (mem_iInter.mp (hj x hx) k)).le
    simpa only [derivativeCoordinates_derivativeFamily] using
      hb.trans_lt (half_lt_self (hε k))

/-- A nonnegative continuous bump on a compact Hausdorff space can be normalized
to have both complex integral and integral of its norm equal to one. -/
theorem exists_normalized_weight [T2Space X] [μ.IsOpenPosMeasure]
    (x₀ : X) {U : Set X} (hU : U ∈ 𝓝 x₀) :
    ∃ a : C(X, ℂ), (∀ x, a x ≠ 0 → x ∈ U) ∧
      (∫ x, a x ∂μ) = 1 ∧ (∫ x, ‖a x‖ ∂μ) = 1 := by
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨f, hf₁, -, hfs, hfr⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hW
      (singleton_subset_iff.mpr hxW)
  have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hfx₀ : f x₀ ≠ 0 := by
    rw [hf₁ (mem_singleton x₀)]
    exact one_ne_zero
  have hfpos : 0 < ∫ x, f x ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero f.continuous hfi (fun x => (hfr x).1)
      hfx₀
  let a : C(X, ℂ) := ⟨fun x => ((f x / (∫ y, f y ∂μ) : ℝ) : ℂ), by fun_prop⟩
  have ha : (∫ x, a x ∂μ) = 1 := by
    change (∫ x, ((f x / (∫ y, f y ∂μ) : ℝ) : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, integral_div, div_self hfpos.ne']
    rfl
  refine ⟨a, ?_, ha, ?_⟩
  · intro x hx
    apply hWU
    apply hfs
    apply subset_closure
    change f x ≠ 0
    intro hfx
    exact hx (by simp [a, hfx])
  · have hn (x : X) : ‖a x‖ = f x / (∫ y, f y ∂μ) := by
      change ‖((f x / (∫ y, f y ∂μ) : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hfr x).1 hfpos.le)]
    simp_rw [hn]
    rw [integral_div, div_self hfpos.ne']

/-- Every member at a point in the compact parameter image is a limit of its
actual weighted compact averages, in the full genuine derivative topology. -/
theorem family_mem_closure_weightAverage_range [T2Space X] [μ.IsOpenPosMeasure]
    (j : C(X, N)) (x₀ : X) :
    derivativeFamily π hv (j x₀) ∈ closure (range (weightAverageLM π μ j hv)) := by
  apply mem_closure_iff_nhds.mpr
  intro V hV
  obtain ⟨U, hU, hUV⟩ := exists_average_neighborhood π hv μ (j x₀) V hV
  obtain ⟨a, haU, ha, hnorm⟩ :=
    exists_normalized_weight μ x₀ (j.continuous.continuousAt hU)
  exact ⟨weightAverageLM π μ j hv a, hUV a j haU ha hnorm, mem_range_self a⟩

/-- Uniformly dense scalar weights suffice to approximate every family vector
over the compact parameter image in its genuine derivative topology. -/
theorem family_mem_closure_dense_weightAverage [T2Space X] [μ.IsOpenPosMeasure]
    (j : C(X, N)) (x₀ : X) {S : Set C(X, ℂ)} (hS : Dense S) :
    derivativeFamily π hv (j x₀) ∈ closure (weightAverageLM π μ j hv '' S) := by
  apply (closure_minimal (t := closure (weightAverageLM π μ j hv '' S)) ?_
    isClosed_closure) (family_mem_closure_weightAverage_range π hv μ j x₀)
  rintro _ ⟨a, rfl⟩
  exact weightAverage_mem_closure_image π μ a j hv hS

/-- Dense scalar weights with averages in a supplied submodule approximate the
original family vector in that submodule's derivative-topology closure. -/
theorem family_mem_closure_of_dense_weightAverage [T2Space X] [μ.IsOpenPosMeasure]
    (j : C(X, N)) (x₀ : X) (M : Submodule ℂ (DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π))
    {S : Set C(X, ℂ)} (hS : Dense S)
    (hM : ∀ a ∈ S, weightAverageLM π μ j hv a ∈ M) :
    derivativeFamily π hv (j x₀) ∈ M.topologicalClosure := by
  apply closure_mono (t := (M : Set (DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π))) ?_
    (family_mem_closure_dense_weightAverage π hv μ j x₀ hS)
  rintro _ ⟨a, ha, rfl⟩
  exact hM a ha

/-- Compact averages of the translates of a genuine smooth vector approximate
that same vector whenever the compact parameter map passes through identity. -/
theorem smoothVector_mem_closure_dense_orbitAverage [T2Space X] [μ.IsOpenPosMeasure]
    (r : C(X, G)) (x₀ : X) (hr : r x₀ = 1)
    (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π)
    {S : Set C(X, ℂ)} (hS : Dense S) :
    w ∈ closure
      (weightAverageLM π (v := fun g => π g
        (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E)) μ r
          (contMDiff_orbit_family π
            (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w).property) '' S) := by
  have h := family_mem_closure_dense_weightAverage π
    (v := fun g => π g (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E))
    (contMDiff_orbit_family π (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w).property)
    μ r x₀ hS
  have he : derivativeFamily π
      (v := fun g => π g (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E))
      (contMDiff_orbit_family π (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w).property)
      (r x₀) = w := by
    apply (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).injective
    apply Subtype.ext
    change π (r x₀) (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E) = _
    rw [hr, map_one, one_apply_eq_self]
  rwa [he] at h

end Langlands.Archimedean.CompactSmoothAverage

namespace Langlands.Archimedean

universe u𝔤 uG uH uN uE uX

/-- Actual compact averages with uniformly dense scalar weights approximate
jointly smooth orbit families in their full genuine derivative topology. -/
def CompactSmoothApproximationStatement : Prop :=
  ∀ (𝔤 : Type u𝔤) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
    [FiniteDimensional ℝ 𝔤]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
    [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold 𝓘(ℝ, H) ∞ N]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (X : Type uX) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (π : G →* (E →L[ℂ] E)) (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (j : C(X, N)) (v : N → E)
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2)))
    (x₀ : X) (S : Set C(X, ℂ)), Dense S →
      CompactSmoothAverage.derivativeFamily π hv (j x₀) ∈
        closure (CompactSmoothAverage.weightAverageLM π μ j hv '' S)

/-- Compact approximation for genuine smooth vectors and all their derivatives. -/
theorem compactSmoothApproximation :
    CompactSmoothApproximationStatement.{u𝔤,uG,uH,uN,uE,uX} := by
  intro 𝔤 _ _ _ G _ _ _ _ H _ _ N _ _ _ E _ _ _ X _ _ _ _ _ π μ _ _ j v hv x₀ S hS
  exact CompactSmoothAverage.family_mem_closure_dense_weightAverage π hv μ j x₀ hS

end Langlands.Archimedean
