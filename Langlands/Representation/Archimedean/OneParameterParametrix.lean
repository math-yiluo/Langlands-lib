import Langlands.Representation.Archimedean.SmoothDerivative
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # A second-order one-parameter parametrix for smooth vectors

For `ε > 0` let `ζ_ε = cutoff ε`, a smooth function equal to `1` on `(-∞, ε/3]` and to `0` on
`[2ε/3, ∞)`. The kernels `a(t) = max(t, 0) ζ_ε(t)` (`secondKernel`) and
`b(t) = -(2 ζ_ε'(t) + t ζ_ε''(t))` (`zerothKernel`) are continuous, vanish outside `(0, ε]`, and
`F(0) = ∫ a F'' + ∫ b F` for every `C²` function `F` (`eq_integral_secondKernel_add`); as
distributions, `δ = a'' + b`.

Along a smooth one-parameter subgroup `γ` the orbit `s ↦ π(γ s) w` of a smooth vector has
derivative `π(γ s) dπ(X) w` with `X = γ'(0)` (`hasDerivAt_orbit_oneParameter`). Applying the
one-variable identity along finitely many one-parameter subgroups in turn
(`exists_sum_integral_curveProd`) writes a smooth vector `w` as
`∑ⱼ ∫ Kⱼ(t) π(γ₀(t₀) ⋯ γ_{m-1}(t_{m-1})) dπ(wordⱼ) w dt` with continuous kernels `Kⱼ` supported in
the closed `ε`-ball. -/

noncomputable section

open scoped Manifold ContDiff Topology
open Set MeasureTheory Filter

namespace Langlands.Archimedean.OneParameterParametrix

/-- The cut-off `ζ_ε(t) = smoothTransition (2 - 3t/ε)`. For `ε > 0` it equals `1` for `t ≤ ε/3`
and `0` for `t ≥ 2ε/3` (`cutoff_eq_one`, `cutoff_eq_zero`). -/
def cutoff (ε t : ℝ) : ℝ := Real.smoothTransition (2 - 3 * t / ε)

theorem contDiff_cutoff (ε : ℝ) : ContDiff ℝ ∞ (cutoff ε) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const ε))

theorem cutoff_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε / 3) : cutoff ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hε]
  linarith

theorem cutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε / 3 ≤ t) : cutoff ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, le_div_iff₀ hε]
  linarith

/-- The derivatives of the cut-off vanish where it is locally constant. -/
theorem deriv_cutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t < ε / 3 ∨ 2 * ε / 3 < t) :
    deriv (cutoff ε) t = 0 ∧ deriv (deriv (cutoff ε)) t = 0 := by
  rcases ht with ht | ht
  · have hU : Iio (ε / 3) ∈ 𝓝 t := Iio_mem_nhds ht
    have h1 : ∀ s ∈ Iio (ε / 3), deriv (cutoff ε) s = 0 := by
      intro s hs
      have : cutoff ε =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds hs] with r hr
        exact cutoff_eq_one hε (le_of_lt hr)
      rw [this.deriv_eq, deriv_const]
    refine ⟨h1 t ht, ?_⟩
    have : deriv (cutoff ε) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [hU] with r hr
      exact h1 r hr
    rw [this.deriv_eq, deriv_const]
  · have hU : Ioi (2 * ε / 3) ∈ 𝓝 t := Ioi_mem_nhds ht
    have h1 : ∀ s ∈ Ioi (2 * ε / 3), deriv (cutoff ε) s = 0 := by
      intro s hs
      have : cutoff ε =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact cutoff_eq_zero hε (le_of_lt hr)
      rw [this.deriv_eq, deriv_const]
    refine ⟨h1 t ht, ?_⟩
    have : deriv (cutoff ε) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [hU] with r hr
      exact h1 r hr
    rw [this.deriv_eq, deriv_const]

/-- The kernel of the second-order term: `a(t) = max(t, 0) ζ_ε(t)`. -/
def secondKernel (ε t : ℝ) : ℝ := max t 0 * cutoff ε t

/-- The kernel of the zeroth-order term: `b(t) = -(2 ζ_ε'(t) + t ζ_ε''(t))`. -/
def zerothKernel (ε t : ℝ) : ℝ :=
  -(2 * deriv (cutoff ε) t + t * deriv (deriv (cutoff ε)) t)

theorem continuous_secondKernel (ε : ℝ) : Continuous (secondKernel ε) :=
  (continuous_id.max continuous_const).mul (contDiff_cutoff ε).continuous

theorem continuous_zerothKernel (ε : ℝ) : Continuous (zerothKernel ε) := by
  have h1 : ContDiff ℝ ∞ (deriv (cutoff ε)) := (contDiff_cutoff ε).iterate_deriv 1
  have h2 : ContDiff ℝ ∞ (deriv (deriv (cutoff ε))) := (contDiff_cutoff ε).iterate_deriv 2
  exact ((continuous_const.mul h1.continuous).add (continuous_id.mul h2.continuous)).neg

theorem secondKernel_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ∉ Ioc 0 ε) : secondKernel ε t = 0 := by
  rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with ht | ht
  · simp [secondKernel, max_eq_right ht]
  · simp [secondKernel, cutoff_eq_zero hε (by linarith : 2 * ε / 3 ≤ t)]

theorem zerothKernel_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ∉ Ioc 0 ε) : zerothKernel ε t = 0 := by
  rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
  have h : t < ε / 3 ∨ 2 * ε / 3 < t := by
    rcases ht with ht | ht
    · left; linarith
    · right; linarith
  obtain ⟨h1, h2⟩ := deriv_cutoff_eq_zero hε h
  simp [zerothKernel, h1, h2]

theorem tsupport_secondKernel_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (secondKernel ε) ⊆ Icc (-ε) ε := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  by_contra h
  exact ht (secondKernel_eq_zero hε fun h' => h ⟨by linarith [h'.1], h'.2⟩)

theorem tsupport_zerothKernel_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (zerothKernel ε) ⊆ Icc (-ε) ε := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  by_contra h
  exact ht (zerothKernel_eq_zero hε fun h' => h ⟨by linarith [h'.1], h'.2⟩)

/-- **The second-order one-variable identity.** For a `C²` function `F` and `ε > 0`,
`F(0) = ∫ a(t) F''(t) dt + ∫ b(t) F(t) dt` with `a = secondKernel ε`, `b = zerothKernel ε`. The
function `Φ = (t ζ) F' - (t ζ)' F` has derivative `a F'' + b F` on `[0, ε]`, `Φ(0) = -F(0)` and
`Φ(ε) = 0`. -/
theorem eq_integral_secondKernel_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {ε : ℝ} (hε : 0 < ε) {F F' F'' : ℝ → V}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : ∀ t, HasDerivAt F' (F'' t) t)
    (hF'' : Continuous F'') :
    F 0 = (∫ t, secondKernel ε t • F'' t) + ∫ t, zerothKernel ε t • F t := by
  set ζ := cutoff ε with hζdef
  have hζ : ContDiff ℝ ∞ ζ := contDiff_cutoff ε
  have hζ1 : ContDiff ℝ ∞ (deriv ζ) := hζ.iterate_deriv 1
  have hdζ : ∀ t, HasDerivAt ζ (deriv ζ t) t := fun t =>
    ((hζ.differentiable (by simp)) t).hasDerivAt
  have hdζ' : ∀ t, HasDerivAt (deriv ζ) (deriv (deriv ζ) t) t := fun t =>
    ((hζ1.differentiable (by simp)) t).hasDerivAt
  set Φ : ℝ → V := fun t => (t * ζ t) • F' t - (ζ t + t * deriv ζ t) • F t with hΦ
  have hΦd : ∀ t, HasDerivAt Φ ((t * ζ t) • F'' t +
      (-(2 * deriv ζ t + t * deriv (deriv ζ) t)) • F t) t := by
    intro t
    have h1 : HasDerivAt (fun t => t * ζ t) (1 * ζ t + t * deriv ζ t) t :=
      (hasDerivAt_id t).mul (hdζ t)
    have h2 : HasDerivAt (fun t => ζ t + t * deriv ζ t)
        (deriv ζ t + (1 * deriv ζ t + t * deriv (deriv ζ) t)) t :=
      (hdζ t).add ((hasDerivAt_id t).mul (hdζ' t))
    have := (h1.smul (hF' t)).sub (h2.smul (hF t))
    convert this using 1
    simp only [one_mul, add_smul, neg_add, neg_smul, two_mul]
    abel
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have hcont : Continuous fun t => (t * ζ t) • F'' t +
      (-(2 * deriv ζ t + t * deriv (deriv ζ) t)) • F t := by
    have h2 : ContDiff ℝ ∞ (deriv (deriv ζ)) := hζ.iterate_deriv 2
    exact ((continuous_id.mul hζ.continuous).smul hF'').add
      (((continuous_const.mul hζ1.continuous).add
        (continuous_id.mul h2.continuous)).neg.smul hFc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := ε)
    (fun t _ => hΦd t) (hcont.intervalIntegrable 0 ε)
  have hΦε : Φ ε = 0 := by
    have hz : ζ ε = 0 := cutoff_eq_zero hε (by linarith)
    have hz' : deriv ζ ε = 0 := (deriv_cutoff_eq_zero hε (Or.inr (by linarith))).1
    simp [hΦ, hz, hz']
  have hΦ0 : Φ 0 = -F 0 := by
    have hz : ζ 0 = 1 := cutoff_eq_one hε (by linarith)
    simp [hΦ, hz]
  rw [hΦε, hΦ0, sub_neg_eq_add, zero_add] at hFTC
  rw [← hFTC]
  have hA : ∀ t ∈ Ioc (0 : ℝ) ε, (t * ζ t) • F'' t +
      (-(2 * deriv ζ t + t * deriv (deriv ζ) t)) • F t =
      secondKernel ε t • F'' t + zerothKernel ε t • F t := by
    intro t ht
    simp [secondKernel, zerothKernel, hζdef, max_eq_left ht.1.le]
  rw [intervalIntegral.integral_of_le hε.le, setIntegral_congr_fun measurableSet_Ioc hA]
  have hi1 : Integrable (fun t => secondKernel ε t • F'' t) (volume.restrict (Ioc 0 ε)) :=
    ((continuous_secondKernel ε).smul hF'').integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi2 : Integrable (fun t => zerothKernel ε t • F t) (volume.restrict (Ioc 0 ε)) :=
    ((continuous_zerothKernel ε).smul hFc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [integral_add hi1 hi2]
  congr 1
  · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [secondKernel_eq_zero hε ht, zero_smul]
  · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [zerothKernel_eq_zero hε ht, zero_smul]

section Group

universe uE uG uV

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G]

/-- Concatenating words composes the iterated derivatives. -/
theorem iteratedLieDerivative_append [TopologicalSpace G] [ChartedSpace E G] {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) (Xs Ys : List E) (v : V) :
    iteratedLieDerivative 𝓘(ℝ, E) π (Xs ++ Ys) v =
      iteratedLieDerivative 𝓘(ℝ, E) π Xs (iteratedLieDerivative 𝓘(ℝ, E) π Ys v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih => simp only [List.cons_append, iteratedLieDerivative_cons, ih]

/-- The ordered product `γ₀(t₀) γ₁(t₁) ⋯ γ_{m-1}(t_{m-1})` of points on `m` curves. -/
def curveProd {m : ℕ} (γ : Fin m → ℝ → G) (t : Fin m → ℝ) : G :=
  (List.ofFn fun i => γ i (t i)).prod

theorem curveProd_zero (γ : Fin 0 → ℝ → G) (t : Fin 0 → ℝ) : curveProd γ t = 1 := by
  simp [curveProd]

theorem curveProd_succ {m : ℕ} (γ : Fin (m + 1) → ℝ → G) (t : Fin (m + 1) → ℝ) :
    curveProd γ t = γ 0 (t 0) * curveProd (Fin.tail γ) (Fin.tail t) := by
  simp [curveProd, List.ofFn_succ, Fin.tail]

theorem continuous_curveProd [TopologicalSpace G] [IsTopologicalGroup G] : ∀ {m : ℕ} (γ : Fin m → ℝ → G),
    (∀ i, Continuous (γ i)) → Continuous (curveProd γ)
  | 0, γ, _ => by
    have : curveProd γ = fun _ => 1 := funext (curveProd_zero γ)
    rw [this]; exact continuous_const
  | m + 1, γ, hγ => by
    have : curveProd γ = fun t => γ 0 (t 0) * curveProd (Fin.tail γ) (Fin.tail t) :=
      funext (curveProd_succ γ)
    rw [this]
    exact ((hγ 0).comp (continuous_apply 0)).mul
      ((continuous_curveProd (Fin.tail γ) fun i => hγ i.succ).comp
        (continuous_pi fun j => continuous_apply j.succ))

variable [TopologicalSpace G] [ChartedSpace E G]

set_option backward.isDefEq.respectTransparency false in
/-- **Derivative along a one-parameter subgroup.** If `γ : ℝ → G` is a smooth homomorphism and `w`
is a smooth vector, then `t ↦ π(γ t) w` has derivative `π(γ t) dπ(X) w` at every `t`, where
`X = γ'(0)` is the tangent vector of `γ` at `0` and `dπ(X)` is `lieDerivative`. -/
theorem hasDerivAt_orbit_oneParameter {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) {γ : ℝ → G} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hγm : ∀ s t, γ (s + t) = γ s * γ t) {w : V} (hw : IsSmoothVector 𝓘(ℝ, E) π w) (t : ℝ) :
    HasDerivAt (fun s => π (γ s) w)
      (π (γ t) (lieDerivative 𝓘(ℝ, E) π (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ)) w)) t := by
  have hγ0 : γ 0 = 1 := by
    have h := hγm 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, V) (orbitMap π w) 1 :=
    hw.mdifferentiableAt (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 := hγ.mdifferentiableAt (by simp)
  have hD : HasDerivAt (orbitMap π w ∘ γ)
      (lieDerivative 𝓘(ℝ, E) π (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ)) w) 0 := by
    have hg' : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, V) (orbitMap π w) (γ 0)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) (orbitMap π w) 1) := by
      rw [hγ0]; exact hg.hasMFDerivAt
    have h1 := hg'.comp (0 : ℝ) hf.hasMFDerivAt
    rw [hasMFDerivAt_iff_hasFDerivAt] at h1
    exact h1.hasDerivAt
  have hL := ((π (γ t)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
  have hL' : HasDerivAt (((π (γ t)).restrictScalars ℝ) ∘ (orbitMap π w ∘ γ))
      (((π (γ t)).restrictScalars ℝ)
        (lieDerivative 𝓘(ℝ, E) π (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ)) w)) (t - t) := by
    rwa [sub_self]
  convert hL'.comp_sub_const t t using 1
  · funext s
    have e := hγm t (s - t)
    rw [add_sub_cancel] at e
    show π (γ s) w = π (γ t) (π (γ (s - t)) w)
    rw [e, map_mul]
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- A bounded operator commuting with `π` commutes with the derivative of a smooth vector. -/
theorem lieDerivative_commute {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) (T : V →L[ℂ] V) (hT : ∀ g v, T (π g v) = π g (T v)) (X : E) {u : V}
    (hu : IsSmoothVector 𝓘(ℝ, E) π u) :
    T (lieDerivative 𝓘(ℝ, E) π X u) = lieDerivative 𝓘(ℝ, E) π X (T u) := by
  let A := T.restrictScalars ℝ
  have hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, V) (orbitMap π u) 1 := hu.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) A (orbitMap π u 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : orbitMap π (T u) = A ∘ orbitMap π u := by
    funext g
    exact (hT g u).symm
  unfold lieDerivative
  rw [he, mfderiv_comp 1 hA hf, ContinuousLinearMap.mfderiv_eq]
  rfl

/-- A bounded operator commuting with `π` maps smooth vectors to smooth vectors. -/
theorem isSmoothVector_of_commute {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) (T : V →L[ℂ] V) (hT : ∀ g v, T (π g v) = π g (T v)) {u : V}
    (hu : IsSmoothVector 𝓘(ℝ, E) π u) : IsSmoothVector 𝓘(ℝ, E) π (T u) := by
  have he : orbitMap π (T u) = (T.restrictScalars ℝ) ∘ orbitMap π u := by
    funext g
    exact (hT g u).symm
  change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (orbitMap π (T u))
  rw [he]
  exact (T.restrictScalars ℝ).contDiff.contMDiff.comp hu

/-- A bounded operator commuting with `π` commutes with every iterated derivative of a smooth
vector. -/
theorem iteratedLieDerivative_commute [LieGroup 𝓘(ℝ, E) ∞ G] {V : Type uV}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (π : G →* (V →L[ℂ] V)) (T : V →L[ℂ] V)
    (hT : ∀ g v, T (π g v) = π g (T v)) (Xs : List E) {u : V}
    (hu : IsSmoothVector 𝓘(ℝ, E) π u) :
    T (iteratedLieDerivative 𝓘(ℝ, E) π Xs u) = iteratedLieDerivative 𝓘(ℝ, E) π Xs (T u) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    have hs : IsSmoothVector 𝓘(ℝ, E) π (iteratedLieDerivative 𝓘(ℝ, E) π Xs u) := by
      have := (smoothIteratedLieDerivative 𝓘(ℝ, E) π Xs ⟨u, hu⟩).property
      rwa [smoothIteratedLieDerivative_apply] at this
    rw [iteratedLieDerivative_cons, iteratedLieDerivative_cons, lieDerivative_commute π T hT X hs,
      ih]

/-- **One step of the iteration.** Averaging against `c(s)` along `γ₀(s)` an expansion over the
remaining curves gives an expansion over all curves, with kernels `c(t₀) Kⱼ(tail t)`. -/
theorem integral_smul_sum_integral_cons [IsTopologicalGroup G] {V : Type uV}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (π : G →* (V →L[ℂ] V))
    (hπ : ∀ v, Continuous fun g => π g v) {m N : ℕ} (γ : Fin (m + 1) → ℝ → G)
    (hγc : ∀ i, Continuous (γ i)) {ε : ℝ} (hε : 0 ≤ ε) {c : ℝ → ℂ} (hc : Continuous c)
    (hcs : tsupport c ⊆ Icc (-ε) ε) {K : Fin N → (Fin m → ℝ) → ℂ} (hK : ∀ j, Continuous (K j))
    (hKs : ∀ j, tsupport (K j) ⊆ Metric.closedBall 0 ε) (v : Fin N → V) :
    ∫ s, c s • π (γ 0 s) (∑ j, ∫ t', K j t' • π (curveProd (Fin.tail γ) t') (v j)) =
      ∑ j, ∫ t, (c (t 0) * K j (Fin.tail t)) • π (curveProd γ t) (v j) := by
  have hΓ' : Continuous (curveProd (Fin.tail γ)) :=
    continuous_curveProd (Fin.tail γ) fun i => hγc i.succ
  have hΓ : Continuous (curveProd γ) := continuous_curveProd γ hγc
  have hKc : ∀ j, HasCompactSupport (K j) := fun j =>
    (isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _) (hKs j)
  -- integrability of the inner integrands
  have hint' : ∀ j, Integrable (fun t' => K j t' • π (curveProd (Fin.tail γ) t') (v j)) :=
    fun j => ((hK j).smul ((hπ (v j)).comp hΓ')).integrable_of_hasCompactSupport
      (hKc j).smul_right
  -- the joint integrand on `ℝ × ℝᵐ`
  have hjoint : ∀ j, Integrable (fun p : ℝ × (Fin m → ℝ) =>
      (c p.1 * K j p.2) • π (γ 0 p.1 * curveProd (Fin.tail γ) p.2) (v j)) := by
    intro j
    have hcont : Continuous (fun p : ℝ × (Fin m → ℝ) =>
        (c p.1 * K j p.2) • π (γ 0 p.1 * curveProd (Fin.tail γ) p.2) (v j)) :=
      ((hc.comp continuous_fst).mul ((hK j).comp continuous_snd)).smul
        ((hπ (v j)).comp (((hγc 0).comp continuous_fst).mul (hΓ'.comp continuous_snd)))
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin m → ℝ) ε)) ?_)
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hcs h')), zero_mul, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs j h')), mul_zero, zero_smul]
  -- the left side, pointwise in `s`
  have hL : ∀ s, c s • π (γ 0 s) (∑ j, ∫ t', K j t' • π (curveProd (Fin.tail γ) t') (v j)) =
      ∑ j, ∫ t', (c s * K j t') • π (γ 0 s * curveProd (Fin.tail γ) t') (v j) := by
    intro s
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← (π (γ 0 s)).integral_comp_comm (hint' j), ← integral_smul]
    congr 1
    funext t'
    rw [map_smul, smul_smul, map_mul]
    rfl
  simp_rw [hL]
  rw [integral_finsetSum _ fun j _ => (hjoint j).integral_prod_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : Integrable (fun t : Fin (m + 1) → ℝ =>
      (c (t 0) * K j (Fin.tail t)) • π (curveProd γ t) (v j)) := by
    refine (((hc.comp (continuous_apply 0)).mul ((hK j).comp
      (continuous_pi fun i => continuous_apply i.succ))).smul
        ((hπ (v j)).comp hΓ)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.smul_right ((isCompact_closedBall 0 ε).of_isClosed_subset
      (isClosed_tsupport _) (Langlands.Analysis.DixmierMalliavin.tsupport_cons_kernel hε hcs (hKs j)))
  rw [Langlands.Analysis.DixmierMalliavin.integral_fin_succ_cons hF]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, curveProd_succ]

/-- **The expansion along finitely many one-parameter subgroups.** For smooth homomorphisms
`γ₀, …, γ_{m-1} : ℝ → G` and `ε > 0` there are finitely many words `wordⱼ` in the model space and
continuous kernels `Kⱼ` on `ℝᵐ` supported in the closed `ε`-ball such that, for every strongly
continuous representation `π` on a complex Banach space and every smooth vector `w`,
`w = ∑ⱼ ∫ Kⱼ(t) π(γ₀(t₀) ⋯ γ_{m-1}(t_{m-1})) dπ(wordⱼ) w dt`. The words and kernels do not depend
on `π`. Induction on `m`: `eq_integral_secondKernel_add` along `γ₀` (with
`hasDerivAt_orbit_oneParameter`) and the expansion over the other curves, combined by
`integral_smul_sum_integral_cons`. -/
theorem exists_sum_integral_curveProd [LieGroup 𝓘(ℝ, E) ∞ G] [IsTopologicalGroup G] {ε : ℝ}
    (hε : 0 < ε) : ∀ {m : ℕ} (γ : Fin m → ℝ → G),
    (∀ i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (γ i)) → (∀ i s t, γ i (s + t) = γ i s * γ i t) →
    ∃ (N : ℕ) (word : Fin N → List E) (K : Fin N → (Fin m → ℝ) → ℂ),
      (∀ j, Continuous (K j) ∧ tsupport (K j) ⊆ Metric.closedBall 0 ε) ∧
      ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (π : G →* (V →L[ℂ] V)), (∀ v, Continuous fun g => π g v) →
        ∀ w, IsSmoothVector 𝓘(ℝ, E) π w →
          w = ∑ j, ∫ t, K j t • π (curveProd γ t)
            (iteratedLieDerivative 𝓘(ℝ, E) π (word j) w)
  | 0, γ, _, _ => by
    refine ⟨1, fun _ => [], fun _ _ => 1, fun _ => ⟨continuous_const, fun t _ => ?_⟩,
      fun V _ _ _ π _ w _ => ?_⟩
    · rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [curveProd_zero, hv]
  | m + 1, γ, hγ, hγm => by
    obtain ⟨N, word, K, hK, hid⟩ :=
      exists_sum_integral_curveProd hε (Fin.tail γ) (fun i => hγ i.succ)
        (fun i => hγm i.succ)
    set X₀ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ 0) 0 (1 : ℝ) with hX₀
    let a : ℝ → ℂ := fun s => (secondKernel ε s : ℂ)
    let b : ℝ → ℂ := fun s => (zerothKernel ε s : ℂ)
    have ha : Continuous a := Complex.continuous_ofReal.comp (continuous_secondKernel ε)
    have hb : Continuous b := Complex.continuous_ofReal.comp (continuous_zerothKernel ε)
    have has : tsupport a ⊆ Icc (-ε) ε :=
      (tsupport_comp_subset Complex.ofReal_zero _).trans (tsupport_secondKernel_subset hε)
    have hbs : tsupport b ⊆ Icc (-ε) ε :=
      (tsupport_comp_subset Complex.ofReal_zero _).trans (tsupport_zerothKernel_subset hε)
    refine ⟨N + N, Fin.append (fun j => word j ++ [X₀, X₀]) word,
      Fin.append (fun j t => a (t 0) * K j (Fin.tail t)) (fun j t => b (t 0) * K j (Fin.tail t)),
      ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(ha.comp (continuous_apply 0)).mul ((hK j).1.comp
            (continuous_pi fun i => continuous_apply i.succ)),
          Langlands.Analysis.DixmierMalliavin.tsupport_cons_kernel hε.le has (hK j).2⟩
      · simp only [Fin.append_right]
        exact ⟨(hb.comp (continuous_apply 0)).mul ((hK j).1.comp
            (continuous_pi fun i => continuous_apply i.succ)),
          Langlands.Analysis.DixmierMalliavin.tsupport_cons_kernel hε.le hbs (hK j).2⟩
    · intro V _ _ _ π hπ w hw
      have hγc : ∀ i, Continuous (γ i) := fun i => (hγ i).continuous
      set w₁ := lieDerivative 𝓘(ℝ, E) π X₀ w with hw₁
      set w₂ := lieDerivative 𝓘(ℝ, E) π X₀ w₁ with hw₂
      have hw₁s : IsSmoothVector 𝓘(ℝ, E) π w₁ := isSmoothVector_lieDerivative _ π X₀ hw
      have hw₂s : IsSmoothVector 𝓘(ℝ, E) π w₂ := isSmoothVector_lieDerivative _ π X₀ hw₁s
      have hγ00 : γ 0 0 = 1 := by
        have h := hγm 0 0 0
        rw [add_zero] at h
        exact left_eq_mul.mp h
      have h1D := eq_integral_secondKernel_add (V := V) hε
        (F := fun s => π (γ 0 s) w) (F' := fun s => π (γ 0 s) w₁)
        (F'' := fun s => π (γ 0 s) w₂)
        (hasDerivAt_orbit_oneParameter π (hγ 0) (hγm 0) hw)
        (hasDerivAt_orbit_oneParameter π (hγ 0) (hγm 0) hw₁s)
        ((hπ w₂).comp (hγc 0))
      simp only [hγ00, map_one, one_apply_eq_self] at h1D
      have hcoe : ∀ (r : ℝ) (x : V), r • x = (r : ℂ) • x := fun r x =>
        (Complex.coe_smul r x).symm
      simp_rw [hcoe] at h1D
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      have e₂ := hid V π hπ w₂ hw₂s
      have e₀ := hid V π hπ w hw
      have step₂ := integral_smul_sum_integral_cons π hπ γ hγc hε.le ha has (fun j => (hK j).1)
        (fun j => (hK j).2) (fun j => iteratedLieDerivative 𝓘(ℝ, E) π (word j) w₂)
      have step₀ := integral_smul_sum_integral_cons π hπ γ hγc hε.le hb hbs (fun j => (hK j).1)
        (fun j => (hK j).2) (fun j => iteratedLieDerivative 𝓘(ℝ, E) π (word j) w)
      rw [← e₂] at step₂
      rw [← e₀] at step₀
      have happ : ∀ j, iteratedLieDerivative 𝓘(ℝ, E) π (word j ++ [X₀, X₀]) w =
          iteratedLieDerivative 𝓘(ℝ, E) π (word j) w₂ := fun j => by
        rw [iteratedLieDerivative_append]
        rfl
      simp only [happ]
      rw [← step₂, ← step₀]
      exact h1D

end Group

end Langlands.Archimedean.OneParameterParametrix
