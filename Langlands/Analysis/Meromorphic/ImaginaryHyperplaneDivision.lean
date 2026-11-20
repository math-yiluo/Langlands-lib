import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Thickening

/-! # Division by real linear forms near the imaginary subspace

Lapid 2011, pp.328–329: a function on `ℂⁿ` whose singularities near a point lie on hyperplanes
with real normal vectors and which stays bounded on the imaginary subspace `iℝⁿ` is holomorphic
there. -/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Real

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic.ImaginaryHyperplane

/-! ## Cauchy estimate for the derivative in several variables -/

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Cauchy's estimate for the Fréchet derivative: if `g` is complex differentiable at every point
of `closedBall y r` and bounded by `M` there, then `‖fderiv ℂ g y‖ ≤ M / r`. -/
theorem norm_fderiv_le_of_forall_mem_closedBall_norm_le {g : E → ℂ} {y : E} {r M : ℝ}
    (hr : 0 < r) (hd : ∀ z ∈ closedBall y r, DifferentiableAt ℂ g z)
    (hM : ∀ z ∈ closedBall y r, ‖g z‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / r := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr.le) fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  set w : E := ((‖u‖ : ℂ)⁻¹) • u with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnu,
      inv_mul_cancel₀ hnu.ne']
  have hmem : ∀ z ∈ closedBall (0 : ℂ) r, y + z • w ∈ closedBall y r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hwn, mul_one]
    simpa using hz
  have hφd : ∀ z ∈ closedBall (0 : ℂ) r,
      HasDerivAt (fun z : ℂ => g (y + z • w)) (fderiv ℂ g (y + z • w) w) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => y + z • w) w z := by
      simpa using ((hasDerivAt_id z).smul_const w).const_add y
    exact (hd _ (hmem z hz)).hasFDerivAt.comp_hasDerivAt z h1
  have hdc : DiffContOnCl ℂ (fun z : ℂ => g (y + z • w)) (ball (0 : ℂ) r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hr.ne']
    exact fun z hz => (hφd z hz).differentiableAt.differentiableWithinAt
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
    (fun z hz => hM _ (hmem z (sphere_subset_closedBall hz)))
  have h0 := (hφd 0 (mem_closedBall_self hr.le)).deriv
  simp only [zero_smul, add_zero] at h0
  rw [h0] at hC
  have hu' : u = (‖u‖ : ℂ) • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hnu.ne'), one_smul]
  calc ‖fderiv ℂ g y u‖ = ‖u‖ * ‖fderiv ℂ g y w‖ := by
        conv_lhs => rw [hu']
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnu]
    _ ≤ ‖u‖ * (M / r) := by gcongr
    _ = M / r * ‖u‖ := mul_comm _ _

end Cauchy

/-! ## Circle averages along a fixed direction depend holomorphically on the base point -/

section Average

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If `g` is holomorphic on an open set `O` containing the circle `s + ζ • V`, `|ζ| = |ρ|`, then
the circle average `x ↦ circleAverage (ζ ↦ g (x + ζ • V)) 0 ρ` is complex differentiable at `s`. -/
theorem differentiableAt_circleAverage_comp_add {g : E → ℂ} {O : Set E} (hO : IsOpen O)
    (hg : DifferentiableOn ℂ g O) (V : E) (ρ : ℝ) {s : E}
    (hs : ∀ ζ ∈ sphere (0 : ℂ) |ρ|, s + ζ • V ∈ O) :
    DifferentiableAt ℂ (fun x => Real.circleAverage (fun ζ => g (x + ζ • V)) 0 ρ) s := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  set K : Set E := (fun ζ : ℂ => s + ζ • V) '' sphere (0 : ℂ) |ρ| with hKdef
  have hK : IsCompact K := (isCompact_sphere 0 |ρ|).image (by fun_prop)
  have hKO : K ⊆ O := by rintro _ ⟨ζ, hζ, rfl⟩; exact hs ζ hζ
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  set r := δ / 2 with hrdef
  have hr : 0 < r := half_pos hδ
  have hKc : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hg.continuousOn.mono hδO)
  have hcirc : ∀ θ : ℝ, s + circleMap 0 ρ θ • V ∈ K := fun θ =>
    ⟨circleMap 0 ρ θ, circleMap_mem_sphere' 0 ρ θ, rfl⟩
  have hball : ∀ x ∈ ball s r, ∀ θ : ℝ,
      closedBall (x + circleMap 0 ρ θ • V) r ⊆ cthickening δ K := by
    intro x hx θ z hz
    apply mem_cthickening_of_dist_le z (s + circleMap 0 ρ θ • V) δ K (hcirc θ)
    have h1 : dist (x + circleMap 0 ρ θ • V) (s + circleMap 0 ρ θ • V) < r := by
      rw [dist_add_right]; exact hx
    have h2 : dist z (x + circleMap 0 ρ θ • V) ≤ r := hz
    linarith [dist_triangle z (x + circleMap 0 ρ θ • V) (s + circleMap 0 ρ θ • V)]
  have hinO : ∀ x ∈ ball s r, ∀ θ : ℝ, x + circleMap 0 ρ θ • V ∈ O := fun x hx θ =>
    hδO (hball x hx θ (mem_closedBall_self hr.le))
  have hdiffAt : ∀ y ∈ O, DifferentiableAt ℂ g y := fun y hy =>
    hg.differentiableAt (hO.mem_nhds hy)
  have hcont : ∀ x ∈ ball s r, Continuous fun θ : ℝ => g (x + circleMap 0 ρ θ • V) := by
    intro x hx
    rw [continuous_iff_continuousAt]
    intro θ
    exact ContinuousAt.comp (g := g) (f := fun θ : ℝ => x + circleMap 0 ρ θ • V)
      (hdiffAt _ (hinO x hx θ)).continuousAt (by fun_prop)
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 2 * π)
    (F := fun x θ => g (x + circleMap 0 ρ θ • V))
    (F' := fun x θ => fderiv ℂ g (x + circleMap 0 ρ θ • V))
    (bound := fun _ => M / r) (x₀ := s) (ball_mem_nhds s hr)
    (Filter.eventually_of_mem (ball_mem_nhds s hr) fun x hx =>
      (hcont x hx).aestronglyMeasurable)
    ((hcont s (mem_ball_self hr)).intervalIntegrable 0 (2 * π))
    (((measurable_fderiv ℂ g).comp (by fun_prop : Measurable fun θ : ℝ =>
      s + circleMap 0 ρ θ • V)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ _ x hx =>
      norm_fderiv_le_of_forall_mem_closedBall_norm_le hr
        (fun z hz => hdiffAt z (hδO (hball x hx θ hz)))
        (fun z hz => hM z (hball x hx θ hz)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ x hx => by
      have h1 := ((hdiffAt _ (hinO x hx θ)).hasFDerivAt).comp x
        ((hasFDerivAt_id x).add_const (circleMap 0 ρ θ • V))
      rw [ContinuousLinearMap.comp_id] at h1
      exact h1)
  have hfun : (fun x => Real.circleAverage (fun ζ => g (x + ζ • V)) 0 ρ) =
      fun x => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, g (x + circleMap 0 ρ θ • V) := by
    funext x
    rw [Real.circleAverage_def]
  rw [hfun]
  exact hderiv.differentiableAt.const_smul ((2 * π)⁻¹ : ℝ)

end Average

/-! ## One variable: division by linear factors with zeros on the imaginary axis -/

section OneVariable

/-- A real inequality between continuous functions at `z₁` follows from the inequality at the
points `z₁ + t i`, `t ≠ 0` small. -/
theorem le_of_eventually_le_along_imaginary {f g : ℂ → ℝ} {z₁ : ℂ} (hf : ContinuousAt f z₁)
    (hg : ContinuousAt g z₁)
    (h : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), f (z₁ + (t : ℂ) * Complex.I) ≤ g (z₁ + (t : ℂ) * Complex.I)) :
    f z₁ ≤ g z₁ := by
  have hγ : Tendsto (fun t : ℝ => z₁ + (t : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝 z₁) := by
    have : Tendsto (fun t : ℝ => z₁ + (t : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 z₁) := by
      have hc : Continuous fun t : ℝ => z₁ + (t : ℂ) * Complex.I := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto (hf.tendsto.comp hγ) (hg.tendsto.comp hγ) h

/-- The root `-b / a` of `b + z a` is imaginary when `b` is imaginary and `a` is real. -/
theorem re_neg_div_eq_zero {a b : ℂ} (ha : a.im = 0) (hb : b.re = 0) : (-b / a).re = 0 := by
  simp [Complex.div_re, ha, hb]

theorem add_mul_eq_mul_sub {a b : ℂ} (ha : a ≠ 0) (z : ℂ) : b + z * a = a * (z - -b / a) := by
  field_simp
  ring

/-- Division by a product of linear factors `b k + z a k` with `a k` real and nonzero and `b k`
imaginary, from a bound on the whole imaginary axis. -/
theorem exists_mul_eq_of_bound_on_imaginary_aux {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    (ha : ∀ k ∈ S, a k ≠ 0) (ha_im : ∀ k ∈ S, (a k).im = 0) (hb : ∀ k ∈ S, (b k).re = 0)
    {R C : ℝ} {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → ‖φ z‖ ≤ C * ‖∏ k ∈ S, (b k + z * a k)‖) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, (∏ k ∈ S, (b k + z * a k)) * ψ z = φ z := by
  classical
  induction S using Finset.induction_on generalizing φ with
  | empty => exact ⟨φ, hφ, fun z _ => by simp⟩
  | @insert k S hk ih =>
    have hak : a k ≠ 0 := ha k (Finset.mem_insert_self k S)
    have ha' : ∀ j ∈ S, a j ≠ 0 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have ha_im' : ∀ j ∈ S, (a j).im = 0 := fun j hj => ha_im j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ S, (b j).re = 0 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    set z₁ : ℂ := -b k / a k with hz₁def
    have hz₁re : z₁.re = 0 :=
      re_neg_div_eq_zero (ha_im k (Finset.mem_insert_self k S)) (hb k (Finset.mem_insert_self k S))
    have hfac : ∀ z, b k + z * a k = a k * (z - z₁) := fun z => add_mul_eq_mul_sub hak z
    have hQcont : Continuous fun z : ℂ => ∏ j ∈ S, (b j + z * a j) := by fun_prop
    by_cases hz₁ : z₁ ∈ ball (0 : ℂ) R
    · have hφz₁ : φ z₁ = 0 := by
        have h1 := hbound z₁ hz₁ hz₁re
        rw [Finset.prod_insert hk, hfac, sub_self, mul_zero, zero_mul, norm_zero, mul_zero] at h1
        exact norm_le_zero_iff.mp h1
      set φ₁ : ℂ → ℂ := fun z => (a k)⁻¹ * dslope φ z₁ z with hφ₁def
      have hφ₁ : DifferentiableOn ℂ φ₁ (ball 0 R) :=
        ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hz₁)).mpr hφ).const_mul _
      have hφeq : ∀ z, (b k + z * a k) * φ₁ z = φ z := by
        intro z
        have h1 := sub_smul_dslope φ z₁ z
        rw [hφz₁, sub_zero, smul_eq_mul] at h1
        rw [hfac, hφ₁def]
        field_simp
        linear_combination h1
      have hne : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ≠ z₁ →
          ‖φ₁ z‖ ≤ C * ‖∏ j ∈ S, (b j + z * a j)‖ := by
        intro z hz hzre hzz
        have h1 := hbound z hz hzre
        rw [Finset.prod_insert hk, norm_mul] at h1
        have h2 : ‖φ z‖ = ‖b k + z * a k‖ * ‖φ₁ z‖ := by
          rw [← hφeq z]
          exact norm_mul _ _
        rw [h2, mul_left_comm] at h1
        have hpos : 0 < ‖b k + z * a k‖ := by
          rw [hfac, norm_pos_iff]
          exact mul_ne_zero hak (sub_ne_zero.mpr hzz)
        exact le_of_mul_le_mul_left h1 hpos
      have hbound₁ : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 →
          ‖φ₁ z‖ ≤ C * ‖∏ j ∈ S, (b j + z * a j)‖ := by
        intro z hz hzre
        by_cases hzz : z = z₁
        · subst hzz
          refine le_of_eventually_le_along_imaginary (f := fun z => ‖φ₁ z‖)
            (g := fun z => C * ‖∏ j ∈ S, (b j + z * a j)‖)
            ((hφ₁.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).norm)
            ((continuous_const.mul hQcont.norm).continuousAt) ?_
          have hball : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), z₁ + (t : ℂ) * Complex.I ∈ ball (0 : ℂ) R := by
            have hc : Continuous fun t : ℝ => z₁ + (t : ℂ) * Complex.I := by fun_prop
            have h0 : (fun t : ℝ => z₁ + (t : ℂ) * Complex.I) 0 ∈ ball (0 : ℂ) R := by
              simpa using hz
            exact nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0))
          filter_upwards [hball, self_mem_nhdsWithin] with t ht htne
          refine hne _ ht (by simp [hz₁re]) ?_
          intro heq
          have : (t : ℂ) * Complex.I = 0 := by linear_combination heq
          simp only [mul_eq_zero, Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false] at this
          exact htne this
        · exact hne z hz hzre hzz
      obtain ⟨ψ, hψ, hψeq⟩ := ih ha' ha_im' hb' hφ₁ hbound₁
      refine ⟨ψ, hψ, fun z hz => ?_⟩
      rw [Finset.prod_insert hk, mul_assoc, hψeq z hz, hφeq]
    · have hden : ∀ z ∈ ball (0 : ℂ) R, b k + z * a k ≠ 0 := by
        intro z hz h0
        rw [hfac] at h0
        have : z = z₁ := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hak)
        exact hz₁ (this ▸ hz)
      set φ₁ : ℂ → ℂ := fun z => φ z / (b k + z * a k) with hφ₁def
      have hφ₁ : DifferentiableOn ℂ φ₁ (ball 0 R) :=
        hφ.div (by fun_prop) hden
      have hbound₁ : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 →
          ‖φ₁ z‖ ≤ C * ‖∏ j ∈ S, (b j + z * a j)‖ := by
        intro z hz hzre
        have h1 := hbound z hz hzre
        rw [Finset.prod_insert hk, norm_mul] at h1
        have hpos : 0 < ‖b k + z * a k‖ := norm_pos_iff.mpr (hden z hz)
        rw [hφ₁def, norm_div, div_le_iff₀ hpos]
        nlinarith
      obtain ⟨ψ, hψ, hψeq⟩ := ih ha' ha_im' hb' hφ₁ hbound₁
      refine ⟨ψ, hψ, fun z hz => ?_⟩
      rw [Finset.prod_insert hk, mul_assoc, hψeq z hz, hφ₁def]
      field_simp [hden z hz]

end OneVariable

section OneVariableClosure

/-- Division by a product of linear factors `b k + z a k` (`a k` real and nonzero, `b k`
imaginary) on `ball 0 R`, from a bound on the imaginary axis away from the zeros of the product. -/
theorem exists_mul_eq_of_bound_on_imaginary {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    (ha : ∀ k ∈ S, a k ≠ 0) (ha_im : ∀ k ∈ S, (a k).im = 0) (hb : ∀ k ∈ S, (b k).re = 0)
    {R C : ℝ} {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → ∏ k ∈ S, (b k + z * a k) ≠ 0 →
      ‖φ z‖ ≤ C * ‖∏ k ∈ S, (b k + z * a k)‖) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, (∏ k ∈ S, (b k + z * a k)) * ψ z = φ z := by
  refine exists_mul_eq_of_bound_on_imaginary_aux S a b ha ha_im hb (C := C) hφ fun z hz hzre => ?_
  by_cases hQ : ∏ k ∈ S, (b k + z * a k) = 0
  swap
  · exact hbound z hz hzre hQ
  have hQcont : Continuous fun z : ℂ => ∏ k ∈ S, (b k + z * a k) := by fun_prop
  refine le_of_eventually_le_along_imaginary (f := fun z => ‖φ z‖)
    (g := fun z => C * ‖∏ k ∈ S, (b k + z * a k)‖)
    ((hφ.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).norm)
    ((continuous_const.mul hQcont.norm).continuousAt) ?_
  have hball : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), z + (t : ℂ) * Complex.I ∈ ball (0 : ℂ) R := by
    have hc : Continuous fun t : ℝ => z + (t : ℂ) * Complex.I := by fun_prop
    have h0 : (fun t : ℝ => z + (t : ℂ) * Complex.I) 0 ∈ ball (0 : ℂ) R := by simpa using hz
    exact nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0))
  have hfac : ∀ k ∈ S, ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      b k + (z + (t : ℂ) * Complex.I) * a k ≠ 0 := by
    intro k hk
    by_cases hzk : b k + z * a k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 : b k + (z + (t : ℂ) * Complex.I) * a k = (t : ℂ) * Complex.I * a k := by
        linear_combination hzk
      rw [h1]
      exact mul_ne_zero (mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero) (ha k hk)
    · have hc : Continuous fun t : ℝ => b k + (z + (t : ℂ) * Complex.I) * a k := by fun_prop
      exact nhdsWithin_le_nhds (hc.continuousAt.eventually_ne (by simpa using hzk))
  filter_upwards [hball, (Filter.eventually_all_finset S).mpr hfac] with t ht hQt
  exact hbound _ ht (by simp [hzre]) (Finset.prod_ne_zero_iff.mpr hQt)

end OneVariableClosure

/-! ## Several variables -/

section SeveralVariables

variable {n : ℕ}

/-- A real direction avoiding the kernels of finitely many complex linear forms that do not vanish
on `ℝⁿ`. -/
theorem exists_real_forall_ne_zero {ι : Type*} [Finite ι] (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hne : ∀ k, ∃ x : Fin n → ℝ, ℓ k (fun t => (x t : ℂ)) ≠ 0) :
    ∃ v : Fin n → ℝ, ∀ k, ℓ k (fun t => (v t : ℂ)) ≠ 0 := by
  set S : ι → Set (Fin n → ℝ) := fun k => {v | ℓ k (fun t => (v t : ℂ)) ≠ 0} with hSdef
  have hcont : ∀ k, Continuous fun v : Fin n → ℝ => ℓ k (fun t => (v t : ℂ)) := fun k =>
    (ℓ k).continuous_of_finiteDimensional.comp (by fun_prop)
  have hopen : ∀ k, IsOpen (S k) := fun k => isOpen_ne_fun (hcont k) continuous_const
  have hdense : ∀ k, Dense (S k) := by
    intro k
    rw [Metric.dense_iff]
    intro v r hr
    by_cases hv : v ∈ S k
    · exact ⟨v, mem_ball_self hr, hv⟩
    obtain ⟨x, hx⟩ := hne k
    set c : ℝ := r / (2 * (‖x‖ + 1)) with hcdef
    have hc : 0 < c := by positivity
    refine ⟨v + c • x, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.le]
      have h1 : c * ‖x‖ ≤ c * (‖x‖ + 1) := by nlinarith [norm_nonneg x]
      have h2 : c * (‖x‖ + 1) = r / 2 := by
        rw [hcdef]; field_simp
      linarith
    · have hv0 : ℓ k (fun t => (v t : ℂ)) = 0 := not_not.mp hv
      have h1 : (fun t => (((v + c • x) t : ℝ) : ℂ)) =
          (fun t => (v t : ℂ)) + (c : ℂ) • (fun t => (x t : ℂ)) := by
        ext t; simp
      show ℓ k (fun t => (((v + c • x) t : ℝ) : ℂ)) ≠ 0
      rw [h1, map_add, map_smul, hv0, zero_add, smul_eq_mul]
      exact mul_ne_zero (by exact_mod_cast hc.ne') hx
  obtain ⟨v, hv⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  exact ⟨v, fun k => Set.mem_iInter.mp hv k⟩

/-- A complex linear form that is real on `ℝⁿ` is imaginary on `iℝⁿ`. -/
theorem re_apply_eq_zero_of_imaginary (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hreal : ∀ x : Fin n → ℝ, (ℓ (fun t => (x t : ℂ))).im = 0) {y : Fin n → ℂ}
    (hy : ∀ t, (y t).re = 0) : (ℓ y).re = 0 := by
  have h1 : y = Complex.I • (fun t => ((y t).im : ℂ)) := by
    ext t
    apply Complex.ext <;> simp [hy t]
  rw [h1, map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
    hreal (fun t => (y t).im)]
  ring

/-- Identity theorem for the totally real subspace `iℝⁿ`: a holomorphic function on a ball
centred on `iℝⁿ` that vanishes on the imaginary points of the ball vanishes on the ball. -/
theorem eqOn_zero_of_eqOn_imaginary {D : (Fin n → ℂ) → ℂ} {s₀ : Fin n → ℂ} {δ : ℝ}
    (hs₀ : ∀ t, (s₀ t).re = 0) (hD : DifferentiableOn ℂ D (ball s₀ δ))
    (hzero : ∀ s ∈ ball s₀ δ, (∀ t, (s t).re = 0) → D s = 0) :
    ∀ s ∈ ball s₀ δ, D s = 0 := by
  intro s hs
  have hδ : 0 < δ := pos_of_mem_ball hs
  set x : Fin n → ℂ := fun t => ((s t).im : ℂ) * Complex.I with hxdef
  set y : Fin n → ℂ := fun t => ((s t).re : ℂ) with hydef
  set γ : ℂ → (Fin n → ℂ) := fun z => x + z • y with hγdef
  have hγd : Differentiable ℂ γ := (differentiable_id.smul_const y).const_add x
  have hγ1 : γ 1 = s := by
    ext t
    apply Complex.ext <;> simp [hγdef, hxdef, hydef]
  set U : Set ℂ := γ ⁻¹' ball s₀ δ with hUdef
  have hU : IsOpen U := isOpen_ball.preimage hγd.continuous
  have hUc : Convex ℝ U := by
    intro z₁ hz₁ z₂ hz₂ p q hp hq hpq
    have h1 : γ (p • z₁ + q • z₂) = p • γ z₁ + q • γ z₂ := by
      ext t
      simp only [hγdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      have : (p : ℂ) + q = 1 := by exact_mod_cast hpq
      linear_combination (-(x t)) * this
    show γ (p • z₁ + q • z₂) ∈ ball s₀ δ
    rw [h1]
    exact convex_ball s₀ δ hz₁ hz₂ hp hq hpq
  have hU0 : (0 : ℂ) ∈ U := by
    show γ 0 ∈ ball s₀ δ
    rw [mem_ball, dist_pi_lt_iff hδ]
    intro t
    have hst : dist (s t) (s₀ t) < δ := (dist_le_pi_dist s s₀ t).trans_lt hs
    have hs0 : s₀ t = ((s₀ t).im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hs₀ t]
    have h1 : γ 0 t - s₀ t = (((s t - s₀ t).im : ℝ) : ℂ) * Complex.I := by
      rw [hs0]; simp [hγdef, hxdef]; ring
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans_lt (by rwa [← dist_eq_norm])
  have hU1 : (1 : ℂ) ∈ U := by
    show γ 1 ∈ ball s₀ δ
    rw [hγ1]; exact hs
  have hDγ : DifferentiableOn ℂ (D ∘ γ) U := hD.comp hγd.differentiableOn (mapsTo_preimage γ _)
  have hγim : ∀ t : ℝ, ∀ u, ((γ ((t : ℂ) * Complex.I)) u).re = 0 := by
    intro t u
    simp [hγdef, hxdef, hydef]
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), (D ∘ γ) ((t : ℂ) * Complex.I) = 0 := by
    have hc : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
    have h0 : (fun t : ℝ => (t : ℂ) * Complex.I) 0 ∈ U := by simpa using hU0
    filter_upwards [nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0))]
      with t ht
    exact hzero _ ht (hγim t)
  have htend : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
      exact (by simpa using hc.tendsto 0 : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I)
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (D ∘ γ) z = 0 := htend.frequently hev.frequently
  have := (hDγ.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero
    hUc.isPreconnected hU0 hfreq hU1
  simpa [hγ1] using this

end SeveralVariables

section Main

variable {n : ℕ}

/-- **Division by real linear forms near the imaginary subspace** (Lapid 2011, pp.328–329). Let
`ℓ k` be finitely many complex linear forms on `ℂⁿ` that are real and not identically zero on
`ℝⁿ`, let `s₀ ∈ iℝⁿ`, and let `h` be holomorphic on an open neighbourhood `W` of `s₀`. If
`‖h s‖ ≤ C ‖∏ k, ℓ k (s - s₀)‖` for the imaginary points `s ∈ W` at which the product does not
vanish, then near `s₀` the function `h` is the product `∏ k, ℓ k (s - s₀)` times a holomorphic
function. -/
theorem exists_differentiableOn_mul_eq_of_norm_le_on_imaginary {ι : Type*} [Fintype ι]
    (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hreal : ∀ k (x : Fin n → ℝ), (ℓ k (fun t => (x t : ℂ))).im = 0)
    (hne : ∀ k, ∃ x : Fin n → ℝ, ℓ k (fun t => (x t : ℂ)) ≠ 0)
    {s₀ : Fin n → ℂ} (hs₀ : ∀ t, (s₀ t).re = 0) {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hs₀W : s₀ ∈ W) {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h W) {C : ℝ}
    (hbound : ∀ s ∈ W, (∀ t, (s t).re = 0) → ∏ k, ℓ k (s - s₀) ≠ 0 →
      ‖h s‖ ≤ C * ‖∏ k, ℓ k (s - s₀)‖) :
    ∃ δ > 0, ∃ c : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ c (ball s₀ δ) ∧
      ∀ s ∈ ball s₀ δ, (∏ k, ℓ k (s - s₀)) * c s = h s := by
  classical
  obtain ⟨v, hv⟩ := exists_real_forall_ne_zero ℓ hne
  set V : Fin n → ℂ := fun t => (v t : ℂ) with hVdef
  set a : ι → ℂ := fun k => ℓ k V with hadef
  have ha : ∀ k, a k ≠ 0 := hv
  have ha_im : ∀ k, (a k).im = 0 := fun k => hreal k v
  set L : (Fin n → ℂ) → ℂ := fun s => ∏ k, ℓ k (s - s₀) with hLdef
  have hℓd : ∀ k, Differentiable ℂ (ℓ k) := fun k => by
    simpa using (LinearMap.toContinuousLinearMap (ℓ k)).differentiable
  have hk : ∀ k, Differentiable ℂ (fun s : Fin n → ℂ => ℓ k (s - s₀)) := fun k =>
    (hℓd k).comp (differentiable_id.sub_const s₀)
  have hLd : Differentiable ℂ L := fun s =>
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun k (s : Fin n → ℂ) => ℓ k (s - s₀))
      fun k _ => ((hk k) s).hasFDerivAt).differentiableAt
  have hLshift : ∀ s (ζ : ℂ), L (s + ζ • V) = ∏ k, (ℓ k (s - s₀) + ζ * a k) := by
    intro s ζ
    simp only [hLdef]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show s + ζ • V - s₀ = (s - s₀) + ζ • V by abel, map_add, map_smul, smul_eq_mul]
  obtain ⟨R₀, hR₀, hR₀W⟩ := Metric.isOpen_iff.mp hW s₀ hs₀W
  set ρ : ℝ := R₀ / (4 * (‖V‖ + 1)) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρV : 2 * ρ * ‖V‖ ≤ R₀ / 2 := by
    have h1 : 2 * ρ * (‖V‖ + 1) = R₀ / 2 := by rw [hρdef]; field_simp; ring
    nlinarith [norm_nonneg V]
  set N : Set (Fin n → ℂ) :=
    ball s₀ (R₀ / 4) ∩ ⋂ k, {s | ‖ℓ k (s - s₀)‖ < ρ * ‖a k‖} with hNdef
  have hN : IsOpen N := isOpen_ball.inter (isOpen_iInter_of_finite fun k =>
    isOpen_lt (hk k).continuous.norm continuous_const)
  have hs₀N : s₀ ∈ N := by
    refine ⟨mem_ball_self (by positivity), mem_iInter.mpr fun k => ?_⟩
    show ‖ℓ k (s₀ - s₀)‖ < ρ * ‖a k‖
    rw [sub_self, map_zero, norm_zero]
    exact mul_pos hρ (norm_pos_iff.mpr (ha k))
  obtain ⟨δ, hδ, hδN⟩ := Metric.isOpen_iff.mp hN s₀ hs₀N
  have hδW : ball s₀ δ ⊆ W := fun s hs =>
    hR₀W (ball_subset_ball (by linarith) (hδN hs).1)
  have hin : ∀ s ∈ ball s₀ δ, ∀ ζ : ℂ, ‖ζ‖ < 2 * ρ → s + ζ • V ∈ W := by
    intro s hs ζ hζ
    apply hR₀W
    have h1 : dist s s₀ < R₀ / 4 := (hδN hs).1
    have h2 : ‖ζ • V‖ ≤ R₀ / 2 := by
      rw [norm_smul]
      nlinarith [norm_nonneg V, norm_nonneg ζ]
    rw [mem_ball]
    calc dist (s + ζ • V) s₀ ≤ dist (s + ζ • V) s + dist s s₀ := dist_triangle _ _ _
      _ = ‖ζ • V‖ + dist s s₀ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ < R₀ := by linarith
  have hfac_ne : ∀ s ∈ ball s₀ δ, ∀ ζ : ℂ, ‖ζ‖ = ρ → ∀ k, ℓ k (s - s₀) + ζ * a k ≠ 0 := by
    intro s hs ζ hζ k h0
    have h1 : ‖ℓ k (s - s₀)‖ < ρ * ‖a k‖ := mem_iInter.mp (hδN hs).2 k
    have h2 : ℓ k (s - s₀) = -(ζ * a k) := eq_neg_of_add_eq_zero_left h0
    rw [h2, norm_neg, norm_mul, hζ] at h1
    exact lt_irrefl _ h1
  set O : Set (Fin n → ℂ) := W ∩ {y | L y ≠ 0} with hOdef
  have hO : IsOpen O := hW.inter (isOpen_ne_fun hLd.continuous continuous_const)
  set g : (Fin n → ℂ) → ℂ := fun y => h y / L y with hgdef
  have hg : DifferentiableOn ℂ g O := fun y hy => by
    have h1 : DifferentiableWithinAt ℂ (fun y => h y * (L y)⁻¹) O y :=
      ((hh y hy.1).mono inter_subset_left).mul ((hLd y).differentiableWithinAt.inv hy.2)
    simpa only [hgdef, div_eq_mul_inv] using h1
  set c : (Fin n → ℂ) → ℂ := fun s => Real.circleAverage (fun ζ => g (s + ζ • V)) 0 ρ
    with hcdef
  have hcirc : ∀ s ∈ ball s₀ δ, ∀ ζ ∈ sphere (0 : ℂ) |ρ|, s + ζ • V ∈ O := by
    intro s hs ζ hζ
    have hζn : ‖ζ‖ = ρ := by simpa [abs_of_pos hρ] using hζ
    refine ⟨hin s hs ζ (by linarith), ?_⟩
    show L (s + ζ • V) ≠ 0
    rw [hLshift]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hfac_ne s hs ζ hζn k
  have hc : DifferentiableOn ℂ c (ball s₀ δ) := fun s hs =>
    (differentiableAt_circleAverage_comp_add hO hg V ρ (hcirc s hs)).differentiableWithinAt
  have hslice : ∀ s ∈ ball s₀ δ, (∀ t, (s t).re = 0) → L s * c s = h s := by
    intro s hs hsre
    set b : ι → ℂ := fun k => ℓ k (s - s₀) with hbdef
    have hb : ∀ k, (b k).re = 0 := fun k =>
      re_apply_eq_zero_of_imaginary (ℓ k) (hreal k) fun t => by simp [hsre t, hs₀ t]
    have hφ : DifferentiableOn ℂ (fun z : ℂ => h (s + z • V)) (ball 0 (2 * ρ)) := by
      intro z hz
      have hzW := hin s hs z (by simpa using hz)
      exact ((hh.differentiableAt (hW.mem_nhds hzW)).comp z
        ((differentiableAt_id.smul_const V).const_add s)).differentiableWithinAt
    obtain ⟨ψ, hψ, hψeq⟩ := exists_mul_eq_of_bound_on_imaginary Finset.univ a b
      (fun k _ => ha k) (fun k _ => ha_im k) (fun k _ => hb k) (C := C) hφ (by
        intro z hz hzre hQ
        have hzW := hin s hs z (by simpa using hz)
        have himag : ∀ t, ((s + z • V) t).re = 0 := by
          intro t
          simp [hVdef, hsre t, hzre]
        have hL : L (s + z • V) = ∏ k, (b k + z * a k) := hLshift s z
        rw [← hL] at hQ ⊢
        exact hbound _ hzW himag hQ)
    have hcs : c s = ψ 0 := by
      show Real.circleAverage (fun ζ => g (s + ζ • V)) 0 ρ = ψ 0
      rw [Real.circleAverage_congr_sphere (f₂ := ψ) ?_]
      · apply DiffContOnCl.circleAverage
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball _ (by positivity : |ρ| ≠ 0)]
        exact hψ.mono (closedBall_subset_ball (by rw [abs_of_pos hρ]; linarith))
      · intro ζ hζ
        have hζn : ‖ζ‖ = ρ := by simpa [abs_of_pos hρ] using hζ
        have hQne : ∏ k, (b k + ζ * a k) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun k _ => hfac_ne s hs ζ hζn k
        have h1 := hψeq ζ (by rw [mem_ball_zero_iff]; linarith)
        show h (s + ζ • V) / L (s + ζ • V) = ψ ζ
        rw [hLshift, ← h1]
        exact mul_div_cancel_left₀ (ψ ζ) hQne
    have h0 := hψeq 0 (mem_ball_self (by positivity))
    simp only [zero_mul, add_zero, zero_smul] at h0
    rw [hcs]
    simpa [hLdef, hbdef] using h0
  have hD : DifferentiableOn ℂ (fun s => L s * c s - h s) (ball s₀ δ) :=
    (hLd.differentiableOn.mul hc).sub (hh.mono hδW)
  refine ⟨δ, hδ, c, hc, fun s hs => sub_eq_zero.mp ?_⟩
  exact eqOn_zero_of_eqOn_imaginary hs₀ hD
    (fun s hs hsre => sub_eq_zero.mpr (hslice s hs hsre)) s hs

end Main

end Langlands.Analysis.Meromorphic.ImaginaryHyperplane
