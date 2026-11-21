import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Compact averages of linear pullbacks of Schwartz functions -/

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzCompactAverage

section Average

variable {Y V W : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (w : Y → ℂ) (A : Y → V →L[ℝ] W) (Φ : 𝓢(W, ℂ))

private def kernel (n : ℕ) (x : V) (y : Y) : V [×n]→L[ℝ] ℂ :=
  w y • iteratedFDeriv ℝ n (Φ ∘ A y) x

omit [CompactSpace Y] in
private theorem continuous_kernel (hw : Continuous w) (hA : Continuous A) (n : ℕ) :
    Continuous (fun p : Y × V => kernel w A Φ n p.2 p.1) := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : Fin n => V) (fun _ : Fin n => W) ℂ
  have hB : Continuous (fun p : Y × V => C (fun _ => A p.1)) :=
    C.cont.comp (continuous_pi fun _ => hA.comp continuous_fst)
  have hD : Continuous (fun p : Y × V => iteratedFDeriv ℝ n Φ (A p.1 p.2)) :=
    ((Φ.smooth ⊤).continuous_iteratedFDeriv (by simp)).comp
      ((hA.comp continuous_fst).clm_apply continuous_snd)
  have h := (hw.comp continuous_fst).smul (hB.clm_apply hD)
  convert h using 1
  funext p
  rw [kernel, (A p.1).iteratedFDeriv_comp_right (Φ.smooth ⊤) p.2 (by simp)]
  rfl

omit [CompactSpace Y] in
/-- Pullback derivatives vary continuously in the linear map and spatial variable. -/
theorem continuous_pullbackDerivative (hA : Continuous A) (n : ℕ) :
    Continuous (fun p : Y × V => iteratedFDeriv ℝ n (Φ ∘ A p.1) p.2) := by
  simpa only [kernel, one_smul] using
    continuous_kernel (fun _ : Y => (1 : ℂ)) A Φ continuous_const hA n

omit [TopologicalSpace Y] [CompactSpace Y] in
private theorem hasFDerivAt_kernel (n : ℕ) (x : V) (y : Y) :
    HasFDerivAt (fun z => kernel w A Φ n z y)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
        (kernel w A Φ (n + 1) x y)) x := by
  have hs : ContDiff ℝ (n + 1 : ℕ) (Φ ∘ A y) := (Φ.smooth _).comp (A y).contDiff
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Φ ∘ A y)) x :=
    (hs.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)).differentiableAt
  have h := hD.hasFDerivAt.const_smul (w y)
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
  have he : L (kernel w A Φ (n + 1) x y) =
      w y • L (iteratedFDeriv ℝ (n + 1) (Φ ∘ A y) x) := by
    ext v m
    rfl
  change HasFDerivAt _ (L (kernel w A Φ (n + 1) x y)) x
  rw [he]
  exact h

private theorem exists_kernel_bound (hw : Continuous w) (hA : Continuous A)
    {H : ℝ} (hH : 0 ≤ H) (hlower : ∀ x y, ‖x‖ ≤ H * ‖A y x‖) (p n : ℕ) :
    ∃ C : ℝ, ∀ x y, ‖x‖ ^ p * ‖kernel w A Φ n x y‖ ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set Y)).exists_bound_of_continuousOn
    hw.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_univ : IsCompact (univ : Set Y)).exists_bound_of_continuousOn
    hA.continuousOn
  obtain ⟨D, hD, hd⟩ := Φ.decay p n
  refine ⟨max B 0 * max L 0 ^ n * H ^ p * D, fun x y => ?_⟩
  have h₁ : ‖kernel w A Φ n x y‖ ≤
      max B 0 * max L 0 ^ n * ‖iteratedFDeriv ℝ n Φ (A y x)‖ := by
    rw [kernel, (A y).iteratedFDeriv_comp_right (Φ.smooth ⊤) x (by simp), norm_smul]
    calc
      _ ≤ ‖w y‖ * (‖iteratedFDeriv ℝ n Φ (A y x)‖ * ∏ _ : Fin n, ‖A y‖) :=
        mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
          (norm_nonneg _)
      _ = ‖w y‖ * ‖A y‖ ^ n * ‖iteratedFDeriv ℝ n Φ (A y x)‖ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
      _ ≤ _ := by
        gcongr
        · exact (hB y (mem_univ _)).trans (le_max_left _ _)
        · exact (hL y (mem_univ _)).trans (le_max_left _ _)
  calc
    _ ≤ (H * ‖A y x‖) ^ p * (max B 0 * max L 0 ^ n * ‖iteratedFDeriv ℝ n Φ (A y x)‖) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hlower x y) _) h₁ (norm_nonneg _) (by positivity)
    _ = max B 0 * max L 0 ^ n * H ^ p * (‖A y x‖ ^ p * ‖iteratedFDeriv ℝ n Φ (A y x)‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hd (A y x)) (by positivity)

variable [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

private theorem integrable_kernel (hw : Continuous w) (hA : Continuous A) (n : ℕ) (x : V) :
    Integrable (kernel w A Φ n x) μ := by
  have hc : Continuous (kernel w A Φ n x) :=
    (continuous_kernel w A Φ hw hA n).comp (continuous_id.prodMk continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable (hw : Continuous w) (hA : Continuous A)
  {H : ℝ} (hH : 0 ≤ H) (hlower : ∀ x y, ‖x‖ ≤ H * ‖A y x‖)

include hw hA hH hlower

private theorem hasFDerivAt_integral_kernel (n : ℕ) (x : V) :
    HasFDerivAt (fun z => ∫ y, kernel w A Φ n z y ∂μ)
      (∫ y, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
        (kernel w A Φ (n + 1) x y) ∂μ) x := by
  obtain ⟨C, hC⟩ := exists_kernel_bound w A Φ hw hA hH hlower 0 (n + 1)
  simp only [pow_zero, one_mul] at hC
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun z y => L (kernel w A Φ (n + 1) z y)) (s := univ) (bound := fun _ => C)
    univ_mem ?_ (integrable_kernel w A Φ μ hw hA n x) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun z => (integrable_kernel w A Φ μ hw hA n z).aestronglyMeasurable
  · have hc : Continuous (fun y => L (kernel w A Φ (n + 1) x y)) :=
      L.continuous.comp ((continuous_kernel w A Φ hw hA (n + 1)).comp
        (continuous_id.prodMk continuous_const))
    exact (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact ae_of_all _ fun y z _ => (L.norm_map _).trans_le (hC z y)
  · exact ae_of_all _ fun y z _ => hasFDerivAt_kernel w A Φ n z y

private theorem iteratedFDeriv_integral (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => ∫ y, w y * Φ (A y x) ∂μ) =
      fun x => ∫ y, kernel w A Φ n x y ∂μ := by
  induction n with
  | zero =>
    funext x
    ext m
    rw [iteratedFDeriv_zero_apply,
      ContinuousMultilinearMap.integral_apply (integrable_kernel w A Φ μ hw hA 0 x)]
    simp only [kernel, smul_apply, iteratedFDeriv_zero_apply,
      Function.comp_apply, smul_eq_mul]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    rw [Function.comp_apply, (hasFDerivAt_integral_kernel w A Φ μ hw hA hH hlower n x).fderiv]
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
    change L.symm (∫ y, L (kernel w A Φ (n + 1) x y) ∂μ) = _
    let L' : (V [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×n]→L[ℝ] ℂ) :=
      L.toContinuousLinearEquiv.toContinuousLinearMap
    have he := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
      (E := V [×(n + 1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×n]→L[ℝ] ℂ) (μ := μ) L'
      (integrable_kernel w A Φ μ hw hA (n + 1) x)
    change (∫ y, L (kernel w A Φ (n + 1) x y) ∂μ) =
        L (∫ y, kernel w A Φ (n + 1) x y ∂μ) at he
    rw [he, L.symm_apply_apply]

/-- The weighted compact average of Schwartz pullbacks by a uniformly bounded-below family
of continuous linear maps is Schwartz. -/
def average : 𝓢(V, ℂ) where
  toFun x := ∫ y, w y * Φ (A y x) ∂μ
  smooth' := by
    apply contDiff_of_differentiable_iteratedFDeriv
    intro n _
    rw [iteratedFDeriv_integral w A Φ μ hw hA hH hlower]
    exact fun x => (hasFDerivAt_integral_kernel w A Φ μ hw hA hH hlower n x).differentiableAt
  decay' p n := by
    rw [iteratedFDeriv_integral w A Φ μ hw hA hH hlower]
    obtain ⟨C, hC⟩ := exists_kernel_bound w A Φ hw hA hH hlower p n
    refine ⟨C * μ.real univ, fun x => ?_⟩
    rw [← Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p), ← norm_smul, ← integral_smul]
    apply norm_integral_le_of_norm_le_const
    exact ae_of_all _ fun y => by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p)]
      exact hC x y

@[simp]
theorem average_apply (x : V) : average w A Φ μ hw hA hH hlower x =
    ∫ y, w y * Φ (A y x) ∂μ := rfl

/-- The iterated derivative of a compact average is the average of the iterated derivatives. -/
theorem iteratedFDeriv_average (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (average w A Φ μ hw hA hH hlower) x =
      ∫ y, w y • iteratedFDeriv ℝ n (Φ ∘ A y) x ∂μ :=
  congrFun (iteratedFDeriv_integral w A Φ μ hw hA hH hlower n) x

omit hw in
/-- The compact average depends continuously on its continuous weight in the uniform norm. -/
theorem continuous_average_weight :
    Continuous (fun b : C(Y, ℂ) => average b A Φ μ b.continuous hA hH hlower) := by
  let I (b : C(Y, ℂ)) := average b A Φ μ b.continuous hA hH hlower
  have hsub (b c : C(Y, ℂ)) : I b - I c = I (b - c) := by
    ext x
    have hc : Continuous (fun y => Φ (A y x)) := Φ.continuous.comp (hA.clm_apply continuous_const)
    have hint (d : C(Y, ℂ)) : Integrable (fun y => d y * Φ (A y x)) μ :=
      (d.continuous.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [I, sub_apply, average_apply, ContinuousMap.sub_apply, sub_mul]
    rw [integral_sub (hint b) (hint c)]
  apply continuous_iff_continuousAt.mpr
  intro c
  apply ((schwartz_withSeminorms ℂ V ℂ).tendsto_nhds I (I c)).2
  rintro ⟨p, n⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  obtain ⟨C, hC⟩ := exists_kernel_bound (fun _ : Y => (1 : ℂ)) A Φ
    continuous_const hA hH hlower p n
  have hbound (b : C(Y, ℂ)) :
      SchwartzMap.seminorm ℂ p n (I b) ≤ (max C 0 * μ.real univ) * ‖b‖ := by
    apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
    intro x
    dsimp only [I]
    rw [iteratedFDeriv_average, ← Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p),
      ← norm_smul, ← integral_smul]
    calc
      _ ≤ (max C 0 * ‖b‖) * μ.real univ := by
        apply norm_integral_le_of_norm_le_const
        exact ae_of_all _ fun y => by
          have hh := (hC x y).trans (le_max_left C 0)
          simp only [kernel, one_smul] at hh
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
          calc
            _ = ‖b y‖ * (‖x‖ ^ p * ‖iteratedFDeriv ℝ n (Φ ∘ A y) x‖) := by ring
            _ ≤ ‖b‖ * max C 0 :=
              mul_le_mul (b.norm_coe_le_norm y) hh (by positivity) (norm_nonneg _)
            _ = _ := mul_comm _ _
      _ = _ := by ring
  have hlim : Tendsto (fun b : C(Y, ℂ) => (max C 0 * μ.real univ) * ‖b - c‖) (𝓝 c) (𝓝 0) := by
    have hc : Continuous (fun b : C(Y, ℂ) => (max C 0 * μ.real univ) * ‖b - c‖) :=
      continuous_const.mul (continuous_id.sub continuous_const).norm
    simpa [ContinuousAt] using hc.continuousAt (x := c)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with b hb
  rw [hsub]
  exact (hbound _).trans_lt hb

end Average

section Recovery

variable {Y V : Type*} [TopologicalSpace Y] [CompactSpace Y] [NormalSpace Y] [T1Space Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (A : Y → V →L[ℝ] V) (hA : Continuous A)
  {H : ℝ} (hH : 0 ≤ H) (hlower : ∀ x y, ‖x‖ ≤ H * ‖A y x‖)
  (Φ : 𝓢(V, ℂ)) (hΦ : HasCompactSupport (Φ : V → ℂ)) {y₀ : Y}
  (h₀ : A y₀ = ContinuousLinearMap.id ℝ V)

include hH hlower hA hΦ h₀

omit [CompactSpace Y] [NormalSpace Y] [T1Space Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem eventually_pullback_deriv_le (p n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : V, ‖x‖ ^ p *
      ‖iteratedFDeriv ℝ n (Φ ∘ A y) x - iteratedFDeriv ℝ n Φ x‖ ≤ ε := by
  obtain ⟨B, hB⟩ := (hΦ.image continuous_norm).bddAbove
  let K := Metric.closedBall (0 : V) (H * max B 0)
  let F (y : Y) (x : V) : V [×n]→L[ℝ] ℂ := (‖x‖ ^ p : ℝ) • iteratedFDeriv ℝ n (Φ ∘ A y) x
  have hF : Continuous (fun q : Y × V => F q.1 q.2) := by
    have h := continuous_kernel (fun _ : Y => (1 : ℂ)) A Φ continuous_const hA n
    have hm : Continuous (fun q : Y × V => iteratedFDeriv ℝ n (Φ ∘ A q.1) q.2) := by
      simpa only [kernel, one_smul] using h
    exact (continuous_snd.norm.pow p).smul hm
  obtain ⟨U, hU, hclose⟩ := (isCompact_closedBall (0 : V) (H * max B 0)).mem_uniformity_of_prod
    (f := F) (s := univ) hF.continuousOn (mem_univ y₀) (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hU
  filter_upwards [hU] with y hy x
  have h₀' : (Φ : V → ℂ) ∘ A y₀ = Φ := by rw [h₀]; rfl
  by_cases hx : x ∈ K
  · have he := hclose y hy x hx
    change dist (F y x) (F y₀ x) < ε at he
    simp only [dist_eq_norm, F, h₀'] at he
    rw [← Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p), ← norm_smul, smul_sub]
    exact he.le
  · have hzero (z : Y) : iteratedFDeriv ℝ n (Φ ∘ A z) x = 0 := by
      by_contra hn
      have hts : x ∈ tsupport ((Φ : V → ℂ) ∘ A z) :=
        support_iteratedFDeriv_subset n hn
      have hsub : tsupport ((Φ : V → ℂ) ∘ A z) ⊆ (A z) ⁻¹' tsupport (Φ : V → ℂ) := by
        apply closure_minimal
        · intro u hu
          exact subset_tsupport Φ hu
        · exact isClosed_closure.preimage (A z).continuous
      have hAz : ‖A z x‖ ≤ B := hB (mem_image_of_mem norm (hsub hts))
      apply hx
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using
        (hlower x z).trans (mul_le_mul_of_nonneg_left (hAz.trans (le_max_left _ _)) hH)
    rw [hzero y, ← h₀', hzero y₀, sub_zero, norm_zero, mul_zero]
    exact hε.le

/-- A compactly supported Schwartz function is in the closure of its pullback averages
with weights from any dense subset of the continuous functions. -/
theorem mem_closure_average_of_dense (S : Set C(Y, ℂ)) (hS : Dense S) :
    Φ ∈ closure ((fun b : C(Y, ℂ) => average b A Φ μ b.continuous hA hH hlower) '' S) := by
  let I (b : C(Y, ℂ)) := average b A Φ μ b.continuous hA hH hlower
  have hI : Continuous I := continuous_average_weight A Φ μ hA hH hlower
  have hrange : range I ⊆ closure (I '' S) := by
    rintro _ ⟨d, rfl⟩
    exact image_closure_subset_closure_image hI (mem_image_of_mem I (hS d))
  apply (closure_minimal hrange isClosed_closure)
  apply (mem_closure_iff_nhds_basis (schwartz_withSeminorms ℂ V ℂ).hasBasis_ball).2
  rintro ⟨s, ε⟩ hε
  have hε' : 0 < ε / 2 := half_pos hε
  let U : Set Y := {y | ∀ i ∈ s, ∀ x : V, ‖x‖ ^ i.1 *
    ‖iteratedFDeriv ℝ i.2 (Φ ∘ A y) x - iteratedFDeriv ℝ i.2 Φ x‖ ≤ ε / 2}
  have hU : U ∈ 𝓝 y₀ := (s.eventually_all.2 fun i _ =>
    eventually_pullback_deriv_le A hA hH hlower Φ hΦ h₀ i.1 i.2 hε')
  obtain ⟨O, hOU, hO, hyO⟩ := mem_nhds_iff.mp hU
  have hdisj : Disjoint Oᶜ ({y₀} : Set Y) := by
    apply disjoint_left.mpr
    intro y hy hs
    rw [mem_singleton_iff] at hs
    exact hy (hs ▸ hyO)
  obtain ⟨b, hb0, hb1, hbpos⟩ :=
    exists_continuous_zero_one_of_isClosed hO.isClosed_compl isClosed_singleton hdisj
  have hbint : Integrable (b : Y → ℝ) μ :=
    b.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let M : ℝ := ∫ y, b y ∂μ
  have hM : 0 < M := integral_pos_of_integrable_nonneg_nonzero (x := y₀) b.continuous hbint
    (fun y => (hbpos y).1) (by
      have he : b y₀ = 1 := hb1 (mem_singleton y₀)
      rw [he]
      exact one_ne_zero)
  let c : C(Y, ℂ) := ⟨fun y => ((b y / M : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (b.continuous.div_const M)⟩
  have hcR : ∫ y, b y / M ∂μ = 1 := by rw [integral_div, div_self hM.ne']
  have hc : ∫ y, c y ∂μ = 1 := by
    change (∫ y, ((b y / M : ℝ) : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, hcR, Complex.ofReal_one]
  have hnon (y : Y) : 0 ≤ b y / M := div_nonneg (hbpos y).1 hM.le
  have hcNorm (y : Y) : ‖c y‖ = b y / M := by
    exact Complex.norm_of_nonneg (hnon y)
  refine ⟨I c, ⟨c, rfl⟩, ?_⟩
  change (s.sup (schwartzSeminormFamily ℂ V ℂ)) (I c - Φ) < ε
  apply Seminorm.finset_sup_apply_lt hε
  rintro ⟨p, n⟩ hi
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ hε'.le
  intro x
  let L (y : Y) := iteratedFDeriv ℝ n (Φ ∘ A y) x
  let L₀ := iteratedFDeriv ℝ n Φ x
  have hsub : iteratedFDeriv ℝ n (⇑(I c - Φ) : V → ℂ) x =
      ∫ y, c y • (L y - L₀) ∂μ := by
    have he : (⇑(I c - Φ) : V → ℂ) = (I c : V → ℂ) - Φ := rfl
    have hi₁ : Integrable (fun y => c y • L y) μ :=
      integrable_kernel c A Φ μ c.continuous hA n x
    have hi₂ : Integrable (fun y => c y • L₀) μ :=
      (c.continuous.smul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [he, iteratedFDeriv_sub_apply ((I c).smooth _).contDiffAt (Φ.smooth _).contDiffAt,
      iteratedFDeriv_average]
    simp only [smul_sub]
    rw [integral_sub hi₁ hi₂, integral_smul_const, hc, one_smul]
  rw [hsub, ← Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p), ← norm_smul, ← integral_smul]
  calc
    _ ≤ ∫ y, ‖‖x‖ ^ p • c y • (L y - L₀)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (ε / 2) * (b y / M) ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((hbint.div_const M).const_mul _)
      exact ae_of_all _ fun y => by
        change ‖‖x‖ ^ p • c y • (L y - L₀)‖ ≤ (ε / 2) * (b y / M)
        by_cases hy : y ∈ O
        · rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), hcNorm]
          calc
            _ = (‖x‖ ^ p * ‖L y - L₀‖) * (b y / M) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (hOU hy (p, n) hi x) (hnon y)
        · have hzero : b y = 0 := hb0 hy
          simp only [hzero, zero_div, mul_zero]
          change ‖‖x‖ ^ p • (((b y / M : ℝ) : ℂ)) • (L y - L₀)‖ ≤ 0
          simp [hzero]
    _ = ε / 2 := by rw [integral_const_mul, hcR, mul_one]

end Recovery

end Langlands.Analysis.SchwartzCompactAverage
