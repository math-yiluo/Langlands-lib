import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv

/-! # A weighted argument principle

Let `f` be holomorphic on an open set `U ⊇ closedBall c R` (with `R > 0`) and nonvanishing on the
circle `sphere c R`, and let `D = divisor f (closedBall c R)` be its divisor of zeros on the closed
disc. For every `φ : ℂ → F` holomorphic on `U`,
`∮_{|t - c| = R} (f'(t) / f(t)) φ(t) dt = 2πi ∑ᶠ u, D(u) φ(u)`.

We also record that `D` has finite support, that `D(u)` is the order of vanishing of `f` at `u`,
and that `D(u) ≠ 0` exactly at the zeros of `f` in the open disc. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Complex MeromorphicOn
open scoped Topology Real

variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}

/-- A function holomorphic near a closed disc and nonvanishing on its boundary circle has
finite order of vanishing at every point of the closed disc. -/
theorem analyticOrderAt_ne_top_of_ne_zero_on_sphere (hR : 0 < R) (hU : IsOpen U)
    (hBU : closedBall c R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hne : ∀ t ∈ sphere c R, f t ≠ 0) {u : ℂ} (hu : u ∈ closedBall c R) :
    analyticOrderAt f u ≠ ⊤ := by
  have hfB : AnalyticOnNhd ℂ f (closedBall c R) := (hf.analyticOnNhd hU).mono hBU
  have hx : c + (R : ℂ) ∈ sphere c R := by
    simp [abs_of_pos hR]
  refine hfB.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
    (sphere_subset_closedBall hx) hu ?_
  rw [(hfB _ (sphere_subset_closedBall hx)).analyticOrderAt_eq_zero.2 (hne _ hx)]
  simp

/-- The divisor of `f` on the closed disc is the order of vanishing of `f`. -/
theorem divisor_closedBall_eq_analyticOrderNatAt (hR : 0 < R) (hU : IsOpen U)
    (hBU : closedBall c R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hne : ∀ t ∈ sphere c R, f t ≠ 0) {u : ℂ} (hu : u ∈ closedBall c R) :
    divisor f (closedBall c R) u = (analyticOrderNatAt f u : ℤ) := by
  have hfB : AnalyticOnNhd ℂ f (closedBall c R) := (hf.analyticOnNhd hU).mono hBU
  rw [hfB.divisor_apply hu,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_ne_zero_on_sphere hR hU hBU hf hne hu)]
  simp

/-- The divisor of `f` on the closed disc is nonzero exactly at the zeros of `f` in the open
disc. -/
theorem divisor_closedBall_ne_zero_iff (hR : 0 < R) (hU : IsOpen U)
    (hBU : closedBall c R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hne : ∀ t ∈ sphere c R, f t ≠ 0) {u : ℂ} :
    divisor f (closedBall c R) u ≠ 0 ↔ u ∈ ball c R ∧ f u = 0 := by
  have hfB : AnalyticOnNhd ℂ f (closedBall c R) := (hf.analyticOnNhd hU).mono hBU
  by_cases hu : u ∈ closedBall c R
  · rw [divisor_closedBall_eq_analyticOrderNatAt hR hU hBU hf hne hu]
    have htop := analyticOrderAt_ne_top_of_ne_zero_on_sphere hR hU hBU hf hne hu
    have hiff : analyticOrderNatAt f u ≠ 0 ↔ f u = 0 := by
      rw [Ne, ← Nat.cast_inj (R := ℕ∞), Nat.cast_analyticOrderNatAt htop, Nat.cast_zero]
      exact (hfB u hu).analyticOrderAt_ne_zero
    rw [Ne, Nat.cast_eq_zero, ← Ne, hiff]
    constructor
    · intro h0
      refine ⟨?_, h0⟩
      rcases (mem_closedBall.1 hu).lt_or_eq with h | h
      · exact h
      · exact absurd h0 (hne u (mem_sphere.2 h))
    · exact fun h => h.2
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h => absurd (ball_subset_closedBall h) hu

/-- The divisor of `f` on the closed disc has finite support. -/
theorem divisor_closedBall_support_finite :
    (divisor f (closedBall c R)).support.Finite :=
  (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Weighted argument principle.** If `f` is holomorphic on an open set containing the closed
disc `closedBall c R` and has no zeros on its boundary circle, then for every `φ` holomorphic on
the same open set, `∮ (f' / f) • φ = 2πi • ∑ᶠ u, D(u) • φ(u)`, where `D` is the divisor of zeros of
`f` on the closed disc. -/
theorem circleIntegral_logDeriv_smul (hR : 0 < R) (hU : IsOpen U) (hBU : closedBall c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hne : ∀ t ∈ sphere c R, f t ≠ 0) {φ : ℂ → F}
    (hφ : DifferentiableOn ℂ φ U) :
    (∮ t in C(c, R), (deriv f t / f t) • φ t) =
      (2 * π * I : ℂ) • ∑ᶠ u, ((divisor f (closedBall c R) u : ℤ) : ℂ) • φ u := by
  set B := closedBall c R with hBdef
  set D := divisor f B with hDdef
  have hfA : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hfB : AnalyticOnNhd ℂ f B := hfA.mono hBU
  have hord : ∀ u : B, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hfB u u.2).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_ne_top_of_ne_zero_on_sphere hR hU hBU hf hne u.2
  have hsupp : D.support.Finite := divisor_closedBall_support_finite
  obtain ⟨g, hgA, hg0, hfg⟩ := hfB.meromorphicOn.extract_zeros_poles hord hsupp
  set S := hsupp.toFinset with hSdef
  set P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u with hPdef
  have hD0 : 0 ≤ D := hfB.divisor_nonneg
  have hDiff : ∀ u, D u ≠ 0 ↔ u ∈ ball c R ∧ f u = 0 := fun u =>
    divisor_closedBall_ne_zero_iff hR hU hBU hf hne
  have hSball : ∀ u ∈ S, u ∈ ball c R := by
    intro u hu
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support] at hu
    exact ((hDiff u).1 hu).1
  have hDsphere : ∀ t ∈ sphere c R, D t = 0 := by
    intro t ht
    by_contra h
    have := ((hDiff t).1 h).1
    rw [mem_ball] at this
    rw [mem_sphere] at ht
    exact lt_irrefl _ (ht ▸ this)
  -- `f = P * g` near every point of the circle
  have hPg : P • g = P * g := by
    ext x
    simp [smul_eq_mul]
  have hloc : ∀ t ∈ sphere c R, f =ᶠ[𝓝 t] P * g := by
    intro t ht
    have htB : t ∈ B := sphere_subset_closedBall ht
    have hPA : AnalyticAt ℂ P t := Function.FactorizedRational.analyticAt (hD0 t)
    have hh : AnalyticAt ℂ (fun x => f x - (P * g) x) t := (hfB t htB).sub (hPA.mul (hgA t htB))
    have hev : ∀ᶠ x in 𝓝[≠] t, x ∈ B → f x = (P * g) x := by
      have := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hfg) t htB
      filter_upwards [this] with x hx hxB
      rcases hx with h | h
      · rw [← hPg]; exact h
      · exact absurd hxB h
    have hfreq : ∃ᶠ x in 𝓝[≠] t, x ∈ ball c R := by
      rw [frequently_nhdsWithin_iff]
      have htcl : t ∈ closure (ball c R) := by
        rw [closure_ball c hR.ne']
        exact htB
      refine (mem_closure_iff_frequently.1 htcl).mono fun x hx => ⟨hx, ?_⟩
      rintro rfl
      rw [mem_ball] at hx
      rw [mem_sphere] at ht
      exact lt_irrefl _ (ht ▸ hx)
    have hz : ∃ᶠ x in 𝓝[≠] t, f x - (P * g) x = 0 :=
      (hfreq.and_eventually hev).mono fun x hx =>
        sub_eq_zero.2 (hx.2 (ball_subset_closedBall hx.1))
    filter_upwards [hh.frequently_zero_iff_eventually_zero.1 hz] with x hx
    exact sub_eq_zero.1 hx
  -- the logarithmic derivative on the circle
  have hPfun : P = fun x => ∏ u ∈ S, (x - u) ^ D u := by
    rw [hPdef, Function.FactorizedRational.finprod_eq_fun hsupp]
    ext x
    refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
    simp only [hSdef, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hu
    simp [h0]
  have hlog : ∀ t ∈ sphere c R,
      deriv f t / f t = ∑ u ∈ S, (D u : ℂ) * (t - u)⁻¹ + deriv g t / g t := by
    intro t ht
    have htB : t ∈ B := sphere_subset_closedBall ht
    have htu : ∀ u ∈ S, t - u ≠ 0 := by
      intro u hu h0
      rw [sub_eq_zero] at h0
      subst h0
      exact absurd (hSball t hu) (by
        rw [mem_ball]; rw [mem_sphere] at ht; exact (lt_irrefl _ <| ht ▸ ·))
    have h1 : deriv f t / f t = logDeriv (P * g) t := by
      rw [← logDeriv_apply, (logDeriv_congr_nhds (hloc t ht)).eq_of_nhds]
    have hPt : P t ≠ 0 := Function.FactorizedRational.ne_zero (hDsphere t ht)
    have hgt : g t ≠ 0 := hg0 ⟨t, htB⟩
    have hPd : DifferentiableAt ℂ P t :=
      (Function.FactorizedRational.analyticAt (hD0 t)).differentiableAt
    rw [h1, logDeriv_mul t hPt hgt hPd (hgA t htB).differentiableAt, logDeriv_apply g]
    congr 1
    rw [hPfun, logDeriv_fun_prod]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [logDeriv_fun_zpow (by fun_prop), logDeriv_apply]
      simp
    · intro u hu
      exact zpow_ne_zero _ (htu u hu)
    · intro u hu
      exact (differentiableAt_id.sub_const u).zpow (Or.inl (htu u hu))
  -- integrate
  have hφB : DifferentiableOn ℂ φ B := hφ.mono hBU
  have hcont_inv' : ∀ u ∈ S,
      ContinuousOn (fun t => (D u : ℂ) • ((t - u)⁻¹ • φ t)) (sphere c R) := by
    intro u hu
    refine continuousOn_const.smul (ContinuousOn.smul ?_ (hφB.continuousOn.mono
      sphere_subset_closedBall))
    refine (continuousOn_id.sub continuousOn_const).inv₀ fun t ht => ?_
    intro h0
    simp only [Pi.sub_apply, id] at h0
    rw [sub_eq_zero] at h0
    have := hSball u hu
    rw [← h0, mem_ball] at this
    rw [mem_sphere] at ht
    exact lt_irrefl _ (ht ▸ this)
  have hcont_inv : ∀ u ∈ S, CircleIntegrable (fun t => (D u : ℂ) • ((t - u)⁻¹ • φ t)) c R :=
    fun u hu => ContinuousOn.circleIntegrable hR.le (hcont_inv' u hu)
  have hcont_sum : CircleIntegrable
      (fun t => ∑ u ∈ S, (D u : ℂ) • ((t - u)⁻¹ • φ t)) c R :=
    ContinuousOn.circleIntegrable hR.le (continuousOn_finsetSum S hcont_inv')
  have hgderiv : DifferentiableOn ℂ (fun t => (deriv g t / g t) • φ t) B := by
    intro t ht
    have hga := hgA t ht
    exact ((hga.deriv.differentiableAt.div hga.differentiableAt (hg0 ⟨t, ht⟩)).smul
      (hφ.differentiableAt (hU.mem_nhds (hBU ht)))).differentiableWithinAt
  have hcont_g : CircleIntegrable (fun t => (deriv g t / g t) • φ t) c R :=
    ContinuousOn.circleIntegrable hR.le (hgderiv.continuousOn.mono sphere_subset_closedBall)
  calc (∮ t in C(c, R), (deriv f t / f t) • φ t)
      = ∮ t in C(c, R), (∑ u ∈ S, (D u : ℂ) • ((t - u)⁻¹ • φ t) +
          (deriv g t / g t) • φ t) := by
        refine circleIntegral.integral_congr hR.le fun t ht => ?_
        rw [hlog t ht, add_smul, Finset.sum_smul]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [mul_smul]
    _ = ∑ u ∈ S, (D u : ℂ) • ∮ t in C(c, R), (t - u)⁻¹ • φ t := by
        rw [circleIntegral.integral_add hcont_sum hcont_g, circleIntegral.integral_fun_sum hcont_inv,
          (hgderiv.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero
            hR.le, add_zero]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [circleIntegral.integral_smul]
    _ = (2 * π * I : ℂ) • ∑ᶠ u, ((D u : ℤ) : ℂ) • φ u := by
        rw [finsum_eq_sum_of_support_subset (s := S), Finset.smul_sum]
        · refine Finset.sum_congr rfl fun u hu => ?_
          rw [hφB.circleIntegral_sub_inv_smul (hSball u hu), smul_comm]
        · intro u hu
          simp only [hSdef, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
          intro h0
          apply hu
          simp [h0]

end Langlands.Analysis.SeveralComplex
