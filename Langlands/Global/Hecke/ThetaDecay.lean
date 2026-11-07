import Langlands.Global.Hecke.MixedSpaceFourier

/-!
# Theta series on the fundamental cone

Let `V = mixedSpace K`. For a coefficient function `a : K → ℂ` supported in a fractional ideal
`I` and bounded, and a function `F` on `V` with Gaussian decay, the theta series
`θ(a, F)(y) = ∑_{γ ∈ K} a(γ) F(γ y)` (`thetaSeries`) converges wherever all coordinates of `y`
are bounded below, and its non-constant part decays like a Gaussian in that lower bound
(`exists_thetaSeries_decay`). On the fundamental cone this gives Gaussian decay in
`N(x) ^ (1 / [K : ℚ])` for `N(x) ≥ 1` (`exists_thetaSeries_decay_cone`) and, for the series
evaluated at `x⁻¹`, Gaussian decay in `N(x) ^ (-1 / [K : ℚ])` for `N(x) ≤ 1`
(`exists_thetaSeries_inv_decay_cone`).

These bounds give the analytic input of the dyadic-cone Mellin functional equation of
`Langlands.Global.Hecke.ConeMellin`: `coneThetaData` builds the theta data on the fundamental
cone from two theta series related by a Poisson summation formula
`θ(a, F)(x) = N(x)⁻¹ θ(b, G)(x⁻¹)` and a weight `χ` that is multiplicative under doubling and
polynomially bounded in `N` on the cone.
-/

open MeasureTheory Set Filter Module
open scoped Topology Classical nonZeroDivisors

noncomputable section

namespace Langlands.Global.Hecke

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

/-! ### Elementary bounds -/

lemma rpow_le_one_add_rpow_abs {u : ℝ} (hu : 1 ≤ u) (a : ℝ) : u ^ a ≤ (1 + u) ^ |a| := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    exact Real.rpow_le_rpow (by linarith) (by linarith) ha
  · calc u ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu ha
      _ ≤ (1 + u) ^ |a| := Real.one_le_rpow (by linarith) (abs_nonneg a)

/-- `e ^ {-c u²} u ^ a ≤ C (1 + u) ^ {-r}` for `u ≥ 1`. -/
lemma exists_exp_neg_mul_sq_mul_rpow_le {c : ℝ} (hc : 0 < c) (a r : ℝ) :
    ∃ C, 0 < C ∧ ∀ u : ℝ, 1 ≤ u → Real.exp (-(c * u ^ 2)) * u ^ a ≤ C * (1 + u) ^ (-r) := by
  obtain ⟨C, hC, hCb⟩ := exists_exp_neg_mul_sq_le_rpow hc (r + |a|)
  refine ⟨C, hC, fun u hu => ?_⟩
  have h1 : 0 < 1 + u := by linarith
  calc Real.exp (-(c * u ^ 2)) * u ^ a ≤ (C * (1 + u) ^ (-(r + |a|))) * (1 + u) ^ |a| :=
        mul_le_mul (hCb u (by linarith)) (rpow_le_one_add_rpow_abs hu a)
          (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = C * (1 + u) ^ (-r) := by
        rw [mul_assoc, ← Real.rpow_add h1, show -(r + |a|) + |a| = -r by ring]

/-- Nonzero vectors of a discrete lattice have norm bounded away from zero. -/
lemma exists_pos_le_norm_of_mem {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] : ∃ δ, 0 < δ ∧ ∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖ := by
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_singleton_iff.mp (isOpen_discrete ({0} : Set L))
  refine ⟨ε, hε, fun x hx hx0 => ?_⟩
  by_contra hlt
  push Not at hlt
  have := h ⟨x, hx⟩ (by rw [dist_zero_right]; exact hlt)
  exact hx0 (congrArg Subtype.val this)

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => mixedSpace K

/-! ### Coordinates and products in the mixed space -/

lemma norm_le_of_normAtPlace_le {x : V} {R : ℝ} (h : ∀ w, normAtPlace w x ≤ R) : ‖x‖ ≤ R := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => h w

/-- If every coordinate of `y` is at least `m`, then `‖z y‖ ≥ m ‖z‖`. -/
lemma mul_norm_le_norm_mul {y : V} {m : ℝ} (hy : ∀ w, m ≤ normAtPlace w y) (z : V) :
    m * ‖z‖ ≤ ‖z * y‖ := by
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun w => normAtPlace w z
  rw [norm_eq_sup'_normAtPlace z, hw]
  calc m * normAtPlace w z ≤ normAtPlace w y * normAtPlace w z :=
        mul_le_mul_of_nonneg_right (hy w) (normAtPlace_nonneg w z)
    _ = normAtPlace w (z * y) := by rw [map_mul, mul_comm]
    _ ≤ ‖z * y‖ := normAtPlace_le_norm w (z * y)

/-! ### Gaussian sums over fractional ideals -/

section IdealLattice

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The embedding of a fractional ideal into its lattice in the mixed space. -/
def toIdealLattice (γ : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) : idealLattice K I :=
  ⟨mixedEmbedding K γ, (mem_idealLattice K I).mpr ⟨γ, γ.2, rfl⟩⟩

lemma toIdealLattice_injective : Function.Injective (toIdealLattice I) := fun _ _ h =>
  Subtype.ext (mixedEmbedding_injective K (congrArg Subtype.val h))

/-- Gaussian sums over a fractional ideal converge. -/
lemma summable_indicator_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
      fun γ : K => Real.exp (-(c * ‖mixedEmbedding K γ‖ ^ 2))) := by
  rw [← summable_subtype_iff_indicator]
  obtain ⟨C, -, hCb⟩ := exists_exp_neg_mul_sq_le_rpow hc ((finrank ℝ V : ℝ) + 1)
  have h := summable_add_zlattice_of_decay (idealLattice K I)
    (G := fun v : V => ((Real.exp (-(c * ‖v‖ ^ 2)) : ℝ) : ℂ)) (C := C) (lt_add_one _)
    (fun v => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hCb _ (norm_nonneg v)) 0
  simp only [zero_add] at h
  refine ((Complex.summable_ofReal.mp h).comp_injective (toIdealLattice_injective I)).congr
    fun γ => ?_
  simp only [Function.comp_apply, toIdealLattice]

end IdealLattice

/-! ### Theta series -/

/-- The theta series `θ(a, F)(y) = ∑_{γ ∈ K} a(γ) F(γ y)`. -/
def thetaSeries (a : K → ℂ) (F : V → ℂ) (y : V) : ℂ :=
  ∑' γ : K, a γ * F (mixedEmbedding K γ * y)

/-- **Decay of theta series.** Let `a` be bounded and supported in the fractional ideal `I`,
and let `F` have Gaussian decay. Fix `m₀ > 0`. Then the terms of the theta series at points
`y` all of whose coordinates are at least `m₀` are bounded by one summable sequence, and if all
coordinates of `y` are at least `m ≥ m₀`, then `|θ(a, F)(y) - a(0) F(0)| ≤ D e ^ {-c' m²}`. -/
theorem exists_thetaSeries_decay (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K → ℂ}
    (ha : ∀ γ, a γ ≠ 0 → γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) {M : ℝ} (hM : ∀ γ, ‖a γ‖ ≤ M)
    {F : V → ℂ} {C c : ℝ} (hc : 0 < c) (hF : ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2)))
    {m₀ : ℝ} (hm₀ : 0 < m₀) :
    ∃ u : K → ℝ, Summable u ∧
      (∀ y : V, (∀ w, m₀ ≤ normAtPlace w y) → ∀ γ, ‖a γ * F (mixedEmbedding K γ * y)‖ ≤ u γ) ∧
      ∃ D c', 0 ≤ D ∧ 0 < c' ∧ ∀ y : V, ∀ m, m₀ ≤ m → (∀ w, m ≤ normAtPlace w y) →
        ‖thetaSeries a F y - a 0 * F 0‖ ≤ D * Real.exp (-(c' * m ^ 2)) := by
  set g : K → ℝ := ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
    (fun γ => Real.exp (-(c * m₀ ^ 2 * ‖mixedEmbedding K γ‖ ^ 2))) with hg_def
  have hg : Summable g := summable_indicator_exp_neg_mul_sq I (by positivity)
  have hg0 : ∀ γ, 0 ≤ g γ := fun γ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) γ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hF 0)
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (Real.exp_pos (-(c * ‖(0 : V)‖ ^ 2)))
    linarith
  have hterm : ∀ y γ, ‖a γ * F (mixedEmbedding K γ * y)‖ ≤
      M * C * Real.exp (-(c * ‖mixedEmbedding K γ * y‖ ^ 2)) := by
    intro y γ
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM γ) (hF _) (norm_nonneg _) hM0
  have hzero : ∀ γ, γ ∉ (I : FractionalIdeal (𝓞 K)⁰ K) → a γ = 0 := fun γ hγ => by
    by_contra h
    exact hγ (ha γ h)
  have hbound : ∀ y : V, (∀ w, m₀ ≤ normAtPlace w y) → ∀ γ,
      ‖a γ * F (mixedEmbedding K γ * y)‖ ≤ M * C * g γ := by
    intro y hy γ
    by_cases hγ : γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
    · refine (hterm y γ).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM0 hC0))
      rw [hg_def, Set.indicator_of_mem (show γ ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) from hγ)]
      refine Real.exp_le_exp.mpr ?_
      have h1 := mul_norm_le_norm_mul hy (mixedEmbedding K γ)
      have h2 : (m₀ * ‖mixedEmbedding K γ‖) ^ 2 ≤ ‖mixedEmbedding K γ * y‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      nlinarith
    · rw [hzero γ hγ, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hM0 hC0) (hg0 γ)
  refine ⟨fun γ => M * C * g γ, hg.mul_left _, hbound, ?_⟩
  obtain ⟨δ, hδ, hδL⟩ := exists_pos_le_norm_of_mem (idealLattice K I)
  refine ⟨M * C * (Real.exp (c * m₀ ^ 2 * δ ^ 2) * ∑' γ, g γ), c * δ ^ 2,
    mul_nonneg (mul_nonneg hM0 hC0) (mul_nonneg (Real.exp_pos _).le (tsum_nonneg hg0)),
    by positivity, fun y m hm hy => ?_⟩
  have hy₀ : ∀ w, m₀ ≤ normAtPlace w y := fun w => hm.trans (hy w)
  have hsum : Summable fun γ => a γ * F (mixedEmbedding K γ * y) :=
    Summable.of_norm_bounded (hg.mul_left (M * C)) (hbound y hy₀)
  rw [thetaSeries, hsum.tsum_eq_add_tsum_ite 0, map_zero, zero_mul, add_sub_cancel_left]
  set E := Real.exp (c * m₀ ^ 2 * δ ^ 2) * Real.exp (-(c * δ ^ 2 * m ^ 2))
  refine (tsum_of_norm_bounded (hg.hasSum.mul_left (M * C * E)) fun γ => ?_).trans_eq
    (by simp only [E]; ring)
  split_ifs with h0
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hC0) (by positivity)) (hg0 γ)
  by_cases hγ : γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
  · refine (hterm y γ).trans ?_
    rw [hg_def, Set.indicator_of_mem (show γ ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) from hγ),
      mul_assoc (M * C)]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM0 hC0)
    set A := ‖mixedEmbedding K γ‖
    set B := ‖mixedEmbedding K γ * y‖
    have hA : δ ≤ A := hδL _ ((mem_idealLattice K I).mpr ⟨γ, hγ, rfl⟩)
      (fun h => h0 (mixedEmbedding_injective K (h.trans (map_zero _).symm)))
    have h1 : m * A ≤ B := mul_norm_le_norm_mul hy _
    have h2 : (m * A) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (hm₀.le.trans hm) (norm_nonneg _)) h1 2
    have h3 : δ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hδ.le hA 2
    have h4 : 0 ≤ m ^ 2 - m₀ ^ 2 := by nlinarith
    have h5 : m₀ ^ 2 * A ^ 2 + δ ^ 2 * m ^ 2 - m₀ ^ 2 * δ ^ 2 ≤ B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h3 h4]
    have h6 := mul_le_mul_of_nonneg_left h5 hc.le
    simp only [E]
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [hzero γ hγ, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hC0) (by positivity)) (hg0 γ)

omit [NumberField K] in
/-- The theta series is continuous on any set on which its terms are bounded by a summable
sequence. -/
lemma continuousOn_tsum_theta {a : K → ℂ} {F : V → ℂ} (hF : Continuous F) {φ : V → V}
    {s : Set V} (hφ : ContinuousOn φ s) {u : K → ℝ} (hu : Summable u)
    (hb : ∀ y ∈ s, ∀ γ, ‖a γ * F (mixedEmbedding K γ * φ y)‖ ≤ u γ) :
    ContinuousOn (fun y => thetaSeries a F (φ y)) s :=
  continuousOn_tsum (fun _ => continuousOn_const.mul
    (hF.comp_continuousOn (continuousOn_const.mul hφ))) hu fun γ y hy => hb y hy γ

/-! ### Decay on the fundamental cone -/

/-- **Decay at the top of the cone.** On the fundamental cone, for `N(x) ≥ 1`, the terms of
the theta series are bounded by one summable sequence and
`|θ(a, F)(x) - a(0) F(0)| ≤ D e ^ {-c' N(x) ^ (2 / [K : ℚ])}`. -/
theorem exists_thetaSeries_decay_cone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K → ℂ}
    (ha : ∀ γ, a γ ≠ 0 → γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) {M : ℝ} (hM : ∀ γ, ‖a γ‖ ≤ M)
    {F : V → ℂ} {C c : ℝ} (hc : 0 < c) (hF : ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) :
    ∃ u : K → ℝ, Summable u ∧ ∃ D c', 0 ≤ D ∧ 0 < c' ∧
      ∀ x ∈ fundamentalCone K, 1 ≤ mixedEmbedding.norm x →
        (∀ γ, ‖a γ * F (mixedEmbedding K γ * x)‖ ≤ u γ) ∧
        ‖thetaSeries a F x - a 0 * F 0‖ ≤
          D * Real.exp (-(c' * (mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹)) ^ 2)) := by
  obtain ⟨r, R, hr, -, hrR⟩ := exists_normAtPlace_bounds (K := K)
  obtain ⟨u, hu, hub, D, c', hD, hc', hdec⟩ := exists_thetaSeries_decay I ha hM hc hF hr
  refine ⟨u, hu, D, c' * r ^ 2, hD, by positivity, fun x hx hN => ?_⟩
  set t := mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹)
  have ht : 1 ≤ t := Real.one_le_rpow hN (by positivity)
  have hy : ∀ w, r * t ≤ normAtPlace w x := fun w => (hrR x hx w).1
  have hy₀ : ∀ w, r ≤ normAtPlace w x := fun w => (le_mul_of_one_le_right hr.le ht).trans (hy w)
  refine ⟨hub x hy₀, ?_⟩
  have := hdec x (r * t) (le_mul_of_one_le_right hr.le ht) hy
  convert this using 4
  ring

/-- **Decay at the bottom of the cone.** On the fundamental cone, for `N(x) ≤ 1`, the terms of
the theta series at `x⁻¹` are bounded by one summable sequence and
`|θ(a, F)(x⁻¹) - a(0) F(0)| ≤ D e ^ {-c' N(x) ^ (-2 / [K : ℚ])}`. -/
theorem exists_thetaSeries_inv_decay_cone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K → ℂ}
    (ha : ∀ γ, a γ ≠ 0 → γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) {M : ℝ} (hM : ∀ γ, ‖a γ‖ ≤ M)
    {F : V → ℂ} {C c : ℝ} (hc : 0 < c) (hF : ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) :
    ∃ u : K → ℝ, Summable u ∧ ∃ D c', 0 ≤ D ∧ 0 < c' ∧
      ∀ x ∈ fundamentalCone K, mixedEmbedding.norm x ≤ 1 →
        (∀ γ, ‖a γ * F (mixedEmbedding K γ * x⁻¹)‖ ≤ u γ) ∧
        ‖thetaSeries a F x⁻¹ - a 0 * F 0‖ ≤
          D * Real.exp (-(c' * ((mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹))⁻¹) ^ 2)) := by
  obtain ⟨r, R, hr, hR, hrR⟩ := exists_normAtPlace_bounds (K := K)
  obtain ⟨u, hu, hub, D, c', hD, hc', hdec⟩ :=
    exists_thetaSeries_decay I ha hM hc hF (inv_pos.mpr hR)
  refine ⟨u, hu, D, c' * (R⁻¹) ^ 2, hD, by positivity, fun x hx hN => ?_⟩
  set t := mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹)
  have hN0 := fundamentalCone.norm_pos_of_mem hx
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have ht : t ≤ 1 := Real.rpow_le_one hN0.le hN (by positivity)
  have ht' : 1 ≤ t⁻¹ := one_le_inv₀ ht0 |>.mpr ht
  have hy : ∀ w, R⁻¹ * t⁻¹ ≤ normAtPlace w x⁻¹ := fun w => by
    rw [normAtPlace_inv, ← mul_inv]
    exact inv_anti₀ (mul_pos hr ht0 |>.trans_le (hrR x hx w).1) (hrR x hx w).2
  have hm : R⁻¹ ≤ R⁻¹ * t⁻¹ := le_mul_of_one_le_right (inv_pos.mpr hR).le ht'
  refine ⟨hub x⁻¹ fun w => hm.trans (hy w), ?_⟩
  have := hdec x⁻¹ (R⁻¹ * t⁻¹) hm hy
  convert this using 4
  ring

/-! ### Integrability on the two halves of the cone -/

section Integrability

lemma norm_rpow_eq_rpow_root {x : V} (hx : x ∈ fundamentalCone K) (a : ℝ) :
    mixedEmbedding.norm x ^ a =
      (mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹)) ^ ((finrank ℚ K : ℝ) * a) := by
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [← Real.rpow_mul (fundamentalCone.norm_pos_of_mem hx).le, ← mul_assoc, inv_mul_cancel₀ hn,
    one_mul]

lemma volume_lower_lt_top : volume (fundamentalDyadicCone (K := K)).lower < ⊤ :=
  (fundamentalCone.isBounded_normLeOne K).measure_lt_top

/-- A function with Gaussian decay in `N(x) ^ (1 / [K : ℚ])` at the top of the cone, times a
weight bounded by a power of `N`, is integrable against every power of `N` there. -/
lemma integrableOn_upper_of_decay {f χ : V → ℂ}
    (hm : AEStronglyMeasurable (fun x => f x * χ x)
      (volume.restrict (fundamentalDyadicCone (K := K)).upper))
    {D c' : ℝ} (hD : 0 ≤ D) (hc' : 0 < c')
    (hf : ∀ x ∈ fundamentalCone K, 1 ≤ mixedEmbedding.norm x →
      ‖f x‖ ≤ D * Real.exp (-(c' * (mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹)) ^ 2)))
    {Kχ τ : ℝ} (hχ : ∀ x ∈ fundamentalCone K, ‖χ x‖ ≤ Kχ * mixedEmbedding.norm x ^ τ)
    (σ : ℝ) :
    IntegrableOn (fun x => ‖f x * χ x‖ * (fundamentalDyadicCone (K := K)).N x ^ σ)
      (fundamentalDyadicCone (K := K)).upper volume := by
  obtain ⟨r, R, hr, hR, hrR⟩ := exists_normAtPlace_bounds (K := K)
  set n := finrank ℚ K
  set d : ℝ := (finrank ℝ V : ℝ)
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_exp_neg_mul_sq_mul_rpow_le hc' (n * (τ + σ)) (d + 1)
  have hint : Integrable (fun x : V => D * |Kχ| * C₁ * (1 + R) ^ (d + 1) * (1 + ‖x‖) ^ (-(d + 1)))
      volume := (integrable_one_add_norm (lt_add_one d)).const_mul _
  refine Integrable.mono' hint.integrableOn
    (hm.norm.mul
      (((fundamentalDyadicCone (K := K)).measurable_N.pow_const σ).aestronglyMeasurable)) ?_
  refine (ae_restrict_mem (fundamentalDyadicCone (K := K)).measurableSet_upper).mono fun x hx => ?_
  have hxC : x ∈ fundamentalCone K := hx.1
  have hN1 : 1 ≤ mixedEmbedding.norm x := le_of_lt hx.2
  have hN0 := fundamentalCone.norm_pos_of_mem hxC
  set t := mixedEmbedding.norm x ^ ((n : ℝ)⁻¹)
  have ht : 1 ≤ t := Real.one_le_rpow hN1 (by positivity)
  have hxt : ‖x‖ ≤ R * t := norm_le_of_normAtPlace_le fun w => (hrR x hxC w).2
  have hNσ : 0 ≤ mixedEmbedding.norm x ^ σ := Real.rpow_nonneg hN0.le _
  simp only [fundamentalDyadicCone_N]
  rw [norm_mul, norm_norm, norm_mul, Real.norm_of_nonneg hNσ, mul_assoc]
  have hχ' : ‖χ x‖ * mixedEmbedding.norm x ^ σ ≤ |Kχ| * t ^ ((n : ℝ) * (τ + σ)) := by
    rw [← norm_rpow_eq_rpow_root hxC, Real.rpow_add hN0, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ((hχ x hxC).trans ?_) hNσ
    exact mul_le_mul_of_nonneg_right (le_abs_self Kχ) (Real.rpow_nonneg hN0.le _)
  have hpoly : (1 + t) ^ (-(d + 1)) ≤ (1 + R) ^ (d + 1) * (1 + ‖x‖) ^ (-(d + 1)) :=
    rpow_neg_le_of_le_mul (by positivity) (by positivity) (by positivity) (by nlinarith)
  calc ‖f x‖ * (‖χ x‖ * mixedEmbedding.norm x ^ σ)
      ≤ (D * Real.exp (-(c' * t ^ 2))) * (|Kχ| * t ^ ((n : ℝ) * (τ + σ))) :=
        mul_le_mul (hf x hxC hN1) hχ' (by positivity) (by positivity)
    _ = D * |Kχ| * (Real.exp (-(c' * t ^ 2)) * t ^ ((n : ℝ) * (τ + σ))) := by ring
    _ ≤ D * |Kχ| * (C₁ * (1 + t) ^ (-(d + 1))) :=
        mul_le_mul_of_nonneg_left (hC₁b t ht) (by positivity)
    _ ≤ D * |Kχ| * (C₁ * ((1 + R) ^ (d + 1) * (1 + ‖x‖) ^ (-(d + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly hC₁.le) (by positivity)
    _ = D * |Kχ| * C₁ * (1 + R) ^ (d + 1) * (1 + ‖x‖) ^ (-(d + 1)) := by ring

/-- A function with Gaussian decay in `N(x) ^ (-1 / [K : ℚ])` at the bottom of the cone, times
a weight bounded by a power of `N`, is integrable against every power of `N` there. -/
lemma integrableOn_lower_of_decay {g χ : V → ℂ}
    (hm : AEStronglyMeasurable (fun x => g x * χ x)
      (volume.restrict (fundamentalDyadicCone (K := K)).lower))
    {D c' : ℝ} (hD : 0 ≤ D) (hc' : 0 < c')
    (hg : ∀ x ∈ fundamentalCone K, mixedEmbedding.norm x ≤ 1 →
      ‖g x‖ ≤ D * Real.exp (-(c' * ((mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹))⁻¹) ^ 2)))
    {Kχ τ : ℝ} (hχ : ∀ x ∈ fundamentalCone K, ‖χ x‖ ≤ Kχ * mixedEmbedding.norm x ^ τ)
    (σ : ℝ) :
    IntegrableOn (fun x => ‖g x * χ x‖ * (fundamentalDyadicCone (K := K)).N x ^ σ)
      (fundamentalDyadicCone (K := K)).lower volume := by
  set n := finrank ℚ K
  obtain ⟨C₂, hC₂, hC₂b⟩ := exists_exp_neg_mul_sq_mul_rpow_le hc' (-(n * (τ + σ))) 0
  refine Integrable.mono' (integrableOn_const (C := D * |Kχ| * C₂) volume_lower_lt_top.ne)
    (hm.norm.mul
      (((fundamentalDyadicCone (K := K)).measurable_N.pow_const σ).aestronglyMeasurable)) ?_
  refine (ae_restrict_mem (fundamentalDyadicCone (K := K)).measurableSet_lower).mono fun x hx => ?_
  have hxC : x ∈ fundamentalCone K := hx.1
  have hN1 : mixedEmbedding.norm x ≤ 1 := hx.2
  have hN0 := fundamentalCone.norm_pos_of_mem hxC
  set t := mixedEmbedding.norm x ^ ((n : ℝ)⁻¹)
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have ht : t ≤ 1 := Real.rpow_le_one hN0.le hN1 (by positivity)
  have ht' : 1 ≤ t⁻¹ := one_le_inv₀ ht0 |>.mpr ht
  have hNσ : 0 ≤ mixedEmbedding.norm x ^ σ := Real.rpow_nonneg hN0.le _
  simp only [fundamentalDyadicCone_N]
  rw [norm_mul, norm_norm, norm_mul, Real.norm_of_nonneg hNσ, mul_assoc]
  have hχ' : ‖χ x‖ * mixedEmbedding.norm x ^ σ ≤ |Kχ| * t⁻¹ ^ (-((n : ℝ) * (τ + σ))) := by
    rw [Real.inv_rpow ht0.le, Real.rpow_neg ht0.le, inv_inv, ← norm_rpow_eq_rpow_root hxC,
      Real.rpow_add hN0, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ((hχ x hxC).trans ?_) hNσ
    exact mul_le_mul_of_nonneg_right (le_abs_self Kχ) (Real.rpow_nonneg hN0.le _)
  calc ‖g x‖ * (‖χ x‖ * mixedEmbedding.norm x ^ σ)
      ≤ (D * Real.exp (-(c' * t⁻¹ ^ 2))) * (|Kχ| * t⁻¹ ^ (-((n : ℝ) * (τ + σ)))) :=
        mul_le_mul (hg x hxC hN1) hχ' (by positivity) (by positivity)
    _ = D * |Kχ| * (Real.exp (-(c' * t⁻¹ ^ 2)) * t⁻¹ ^ (-((n : ℝ) * (τ + σ)))) := by ring
    _ ≤ D * |Kχ| * (C₂ * (1 + t⁻¹) ^ (-(0 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hC₂b t⁻¹ ht') (by positivity)
    _ = D * |Kχ| * C₂ := by rw [neg_zero, Real.rpow_zero, mul_one]

/-- A weight bounded by a power of `N` on the cone is integrable on the first shell. -/
lemma integrableOn_piece_zero_of_bound {χ : V → ℂ}
    (hm : AEStronglyMeasurable χ (volume.restrict (fundamentalCone K)))
    {Kχ τ : ℝ} (hχ : ∀ x ∈ fundamentalCone K, ‖χ x‖ ≤ Kχ * mixedEmbedding.norm x ^ τ) :
    IntegrableOn χ ((fundamentalDyadicCone (K := K)).piece 0) volume := by
  have hsub : (fundamentalDyadicCone (K := K)).piece 0 ⊆ (fundamentalDyadicCone (K := K)).lower :=
    fun x hx =>
    ⟨hx.1, ((fundamentalDyadicCone (K := K)).level_nonpos_iff hx.1).mp hx.2.le⟩
  refine Integrable.mono'
    (integrableOn_const (C := |Kχ| * Real.exp (|τ| * ((finrank ℝ V : ℝ) * Real.log 2)))
      ((measure_mono hsub).trans_lt volume_lower_lt_top).ne)
    (hm.mono_measure (Measure.restrict_mono (fun x hx => hx.1) le_rfl)) ?_
  refine (ae_restrict_mem ((fundamentalDyadicCone (K := K)).measurableSet_piece 0)).mono
    fun x hx => ?_
  have hN0 := fundamentalCone.norm_pos_of_mem (show x ∈ fundamentalCone K from hx.1)
  refine (hχ x hx.1).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self Kχ) (Real.rpow_nonneg hN0.le _)).trans ?_
  exact mul_le_mul_of_nonneg_left ((fundamentalDyadicCone (K := K)).rpow_le_of_mem_piece_zero hx τ)
    (abs_nonneg _)

end Integrability

/-! ### Theta data on the fundamental cone -/

lemma continuousOn_inv_lower :
    ContinuousOn (fun x : V => x⁻¹) (fundamentalDyadicCone (K := K)).lower := fun _ hx =>
  (hasFDerivAt_inv' (fundamentalCone.norm_pos_of_mem hx.1).ne').continuousAt.continuousWithinAt

section ThetaData

variable (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a b : K → ℂ}
  (ha : ∀ γ, a γ ≠ 0 → γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K))
  (hb : ∀ γ, b γ ≠ 0 → γ ∈ (J : FractionalIdeal (𝓞 K)⁰ K))
  (ha_bdd : ∃ M, ∀ γ, ‖a γ‖ ≤ M) (hb_bdd : ∃ M, ∀ γ, ‖b γ‖ ≤ M)
  {F G : mixedSpace K → ℂ} (hFc : Continuous F) (hGc : Continuous G)
  (hF : ∃ C c, 0 < c ∧ ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2)))
  (hG : ∃ C c, 0 < c ∧ ∀ z, ‖G z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2)))
  {χ : mixedSpace K → ℂ} (hχm : AEStronglyMeasurable χ (volume.restrict (fundamentalCone K)))
  (hχb : ∃ Kχ τ : ℝ, ∀ x ∈ fundamentalCone K, ‖χ x‖ ≤ Kχ * mixedEmbedding.norm x ^ τ)

include ha ha_bdd hFc hF hχm in
lemma aestronglyMeasurable_thetaSeries_upper :
    AEStronglyMeasurable (fun x => (thetaSeries a F x - a 0 * F 0) * χ x)
      (volume.restrict (fundamentalDyadicCone (K := K)).upper) := by
  obtain ⟨M, hM⟩ := ha_bdd
  obtain ⟨C, c, hc, hFb⟩ := hF
  obtain ⟨u, hu, _, _, _, _, h⟩ := exists_thetaSeries_decay_cone I ha hM hc hFb
  have hcont : ContinuousOn (fun x => thetaSeries a F (id x))
      (fundamentalDyadicCone (K := K)).upper :=
    continuousOn_tsum_theta hFc continuousOn_id hu fun y hy => (h y hy.1 hy.2.le).1
  exact ((hcont.sub continuousOn_const).aestronglyMeasurable
    (fundamentalDyadicCone (K := K)).measurableSet_upper).mul
    (hχm.mono_measure (Measure.restrict_mono (fun x hx => hx.1) le_rfl))

include hb hb_bdd hGc hG hχm in
lemma aestronglyMeasurable_thetaSeries_lower :
    AEStronglyMeasurable (fun x => (thetaSeries b G x⁻¹ - b 0 * G 0) * χ x)
      (volume.restrict (fundamentalDyadicCone (K := K)).lower) := by
  obtain ⟨M, hM⟩ := hb_bdd
  obtain ⟨C, c, hc, hGb⟩ := hG
  obtain ⟨u, hu, _, _, _, _, h⟩ := exists_thetaSeries_inv_decay_cone J hb hM hc hGb
  have hcont : ContinuousOn (fun x => thetaSeries b G x⁻¹)
      (fundamentalDyadicCone (K := K)).lower :=
    continuousOn_tsum_theta hGc continuousOn_inv_lower hu fun y hy => (h y hy.1 hy.2).1
  exact ((hcont.sub continuousOn_const).aestronglyMeasurable
    (fundamentalDyadicCone (K := K)).measurableSet_lower).mul
    (hχm.mono_measure (Measure.restrict_mono (fun x hx => hx.1) le_rfl))

include ha ha_bdd hFc hF hχm hχb in
lemma integrableOn_thetaSeries_upper (σ : ℝ) :
    IntegrableOn (fun x => ‖(thetaSeries a F x - a 0 * F 0) * χ x‖ *
      (fundamentalDyadicCone (K := K)).N x ^ σ) (fundamentalDyadicCone (K := K)).upper volume := by
  have hm := aestronglyMeasurable_thetaSeries_upper I ha ha_bdd hFc hF hχm
  obtain ⟨M, hM⟩ := ha_bdd
  obtain ⟨C, c, hc, hFb⟩ := hF
  obtain ⟨Kχ, τ, hχ⟩ := hχb
  obtain ⟨_, _, D, c', hD, hc', h⟩ := exists_thetaSeries_decay_cone I ha hM hc hFb
  exact integrableOn_upper_of_decay hm hD hc' (fun x hx hN => (h x hx hN).2) hχ σ

include hb hb_bdd hGc hG hχm hχb in
lemma integrableOn_thetaSeries_lower (σ : ℝ) :
    IntegrableOn (fun x => ‖(thetaSeries b G x⁻¹ - b 0 * G 0) * χ x‖ *
      (fundamentalDyadicCone (K := K)).N x ^ σ) (fundamentalDyadicCone (K := K)).lower volume := by
  have hm := aestronglyMeasurable_thetaSeries_lower J hb hb_bdd hGc hG hχm
  obtain ⟨M, hM⟩ := hb_bdd
  obtain ⟨C, c, hc, hGb⟩ := hG
  obtain ⟨Kχ, τ, hχ⟩ := hχb
  obtain ⟨_, _, D, c', hD, hc', h⟩ := exists_thetaSeries_inv_decay_cone J hb hM hc hGb
  exact integrableOn_lower_of_decay hm hD hc' (fun x hx hN => (h x hx hN).2) hχ σ

/-- **Theta data on the fundamental cone.** Two theta series `θ(a, F)` and `θ(b, G)` with
coefficients bounded and supported in fractional ideals and continuous Gaussian-decaying `F`,
`G`, related by the Poisson summation formula `θ(a, F)(x) = N(x)⁻¹ θ(b, G)(x⁻¹)` on the cone,
together with a weight `χ` satisfying `χ(2x) = l χ(x)` and `|χ(x)| ≤ K N(x) ^ τ` on the cone,
give theta data with `f = θ(a, F) - a(0) F(0)` and `g(x) = θ(b, G)(x⁻¹) - b(0) G(0)`. -/
def coneThetaData
    (hpoisson : ∀ x ∈ fundamentalCone K,
      thetaSeries a F x = (mixedEmbedding.norm x : ℂ)⁻¹ * thetaSeries b G x⁻¹)
    {l : ℂ} (hl : l ≠ 0) (hχ2 : ∀ x ∈ fundamentalCone K, χ ((2 : ℝ) • x) = l * χ x) :
    (fundamentalDyadicCone (K := K)).ThetaData volume where
  χ := χ
  l := l
  l_ne_zero := hl
  χ_two_smul := hχ2
  integrableOn_χ := by
    obtain ⟨Kχ, τ, h⟩ := hχb
    exact integrableOn_piece_zero_of_bound hχm h
  f x := thetaSeries a F x - a 0 * F 0
  g x := thetaSeries b G x⁻¹ - b 0 * G 0
  A := a 0 * F 0
  B := b 0 * G 0
  f_add x hx := by
    simp only [sub_add_cancel]
    exact hpoisson x hx
  aestronglyMeasurable_f := aestronglyMeasurable_thetaSeries_upper I ha ha_bdd hFc hF hχm
  aestronglyMeasurable_g := aestronglyMeasurable_thetaSeries_lower J hb hb_bdd hGc hG hχm
  integrableOn_f := integrableOn_thetaSeries_upper I ha ha_bdd hFc hF hχm hχb
  integrableOn_g := integrableOn_thetaSeries_lower J hb hb_bdd hGc hG hχm hχb

end ThetaData

end Langlands.Global.Hecke
