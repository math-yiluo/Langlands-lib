import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Schwartz continuity for smooth families on a common compact support -/

noncomputable section

open Filter Set
open scoped ContDiff SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzCompactFamilies

universe u v w

section Continuity

variable {P : Type u} {E : Type v} {F : Type w}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth function vanishing off a compact set, regarded as a Schwartz map. -/
def ofCompactSupport (f : E → F) (hf : ContDiff ℝ ∞ f) (S : Set E) (hS : IsCompact S)
    (hZero : ∀ x ∉ S, f x = 0) : 𝓢(E, F) := by
  have hSupport : Function.support f ⊆ S := by
    intro x hx
    by_contra h
    exact hx (hZero x h)
  have hCompact : HasCompactSupport f :=
    hS.of_isClosed_subset isClosed_closure (closure_minimal hSupport hS.isClosed)
  exact hCompact.toSchwartzMap hf

@[simp] theorem ofCompactSupport_apply (f : E → F) (hf : ContDiff ℝ ∞ f) (S : Set E)
    (hS : IsCompact S) (hZero : ∀ x ∉ S, f x = 0) (x : E) :
    ofCompactSupport f hf S hS hZero x = f x := rfl

/-- The iterated spatial derivatives of a jointly smooth function are jointly smooth. -/
theorem contDiff_iteratedFDeriv_slice {f : P × E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : P × E => iteratedFDeriv ℝ n (fun x : E => f (p.1, x)) p.2) := by
  let ι := ContinuousLinearMap.inr ℝ P E
  let C := ContinuousMultilinearMap.compContinuousLinearMapL (F := F) (fun _ : Fin n => ι)
  have hEq :
      (fun p : P × E => C (iteratedFDeriv ℝ n f p)) =
        fun p => iteratedFDeriv ℝ n (fun x : E => f (p.1, x)) p.2 := by
    funext p
    let fₚ : P × E → F := fun y => f ((p.1, 0) + y)
    have hfₚ : ContDiff ℝ ∞ fₚ := hf.comp (contDiff_const.add contDiff_id)
    have hSlice : (fun x : E => f (p.1, x)) = fₚ ∘ ι := by
      funext x
      simp [fₚ, ι]
    rw [hSlice]
    change (iteratedFDeriv ℝ n f p).compContinuousLinearMap (fun _ => ι) =
      iteratedFDeriv ℝ n (fₚ ∘ ι) p.2
    rw [ι.iteratedFDeriv_comp_right hfₚ p.2 (by simp)]
    rw [show fₚ = (fun y => f ((p.1, 0) + y)) from rfl, iteratedFDeriv_comp_add_left]
    simp [ι]
  rw [← hEq]
  exact C.contDiff.comp (hf.iteratedFDeriv_right (by simp))

/-- Joint smoothness and a common compact support give continuity into Schwartz space. -/
def SchwartzCompactFamilyContinuityStatement : Prop :=
  ∀ (P : Type u) (E : Type v) (F : Type w)
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : P → 𝓢(E, F)) (S : Set E), IsCompact S →
    (∀ p x, x ∉ S → Φ p x = 0) → ContDiff ℝ ∞ (fun y : P × E => Φ y.1 y.2) → Continuous Φ

theorem schwartzCompactFamilyContinuity : SchwartzCompactFamilyContinuityStatement.{u, v, w} := by
  intro P E F _ _ _ _ _ _ Φ S hS hSupport hSmooth
  rw [continuous_iff_continuousAt]
  intro p₀
  apply ((schwartz_withSeminorms ℝ E F).tendsto_nhds Φ (Φ p₀)).mpr
  rintro ⟨k, n⟩ ε hε
  let D (y : P × E) := iteratedFDeriv ℝ n (fun x => Φ y.1 x) y.2
  have hD : Continuous D := (contDiff_iteratedFDeriv_slice hSmooth n).continuous
  let B (y : P × E) := ‖y.2‖ ^ k * ‖D y - D (p₀, y.2)‖
  have hB : Continuous B := (continuous_snd.norm.pow k).mul
      (hD.sub (hD.comp (continuous_const.prodMk continuous_snd))).norm
  have hLocal : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ S, B (p, x) < ε / 2 := by
    apply hS.eventually_forall_of_forall_eventually
    intro x _
    apply (hB.continuousAt (x := (p₀, x))).eventually_lt continuousAt_const
    simpa only [B, sub_self, norm_zero, mul_zero] using half_pos hε
  filter_upwards [hLocal] with p hp
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le ?_) (half_lt_self hε)
  intro x
  by_cases hx : x ∈ S
  · change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(Φ p) - ⇑(Φ p₀)) x‖ ≤ ε / 2
    rw [iteratedFDeriv_sub_apply ((Φ p).smooth _).contDiffAt ((Φ p₀).smooth _).contDiffAt]
    exact (hp x hx).le
  · have hZero : (⇑(Φ p) - ⇑(Φ p₀)) =ᶠ[𝓝 x] (fun _ : E => (0 : F)) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [Pi.sub_apply, hSupport p y hy, hSupport p₀ y hy, sub_zero]
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(Φ p) - ⇑(Φ p₀)) x‖ ≤ ε / 2
    rw [(hZero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    simpa only [Pi.zero_apply, norm_zero, mul_zero] using (half_pos hε).le

end Continuity

section Exponential

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiply a test by a spectral exponential on its compact support. -/
def exponentialTest (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (Φ : 𝓢(E, ℂ))
    (S : Set E) (hS : IsCompact S) (hSupport : ∀ x ∉ S, Φ x = 0) (z : ℂ) : 𝓢(E, ℂ) :=
  ofCompactSupport (fun x => Complex.exp (z * b x) * Φ x)
    ((contDiff_const.mul hb).cexp.mul (Φ.smooth ⊤)) S hS
    (fun x hx => by rw [hSupport x hx, mul_zero])

@[simp] theorem exponentialTest_apply (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (Φ : 𝓢(E, ℂ))
    (S : Set E) (hS : IsCompact S) (hSupport : ∀ x ∉ S, Φ x = 0) (z : ℂ) (x : E) :
    exponentialTest b hb Φ S hS hSupport z x = Complex.exp (z * b x) * Φ x := rfl

private theorem contDiff_expDividedDifference : ContDiff ℝ ∞ (dslope Complex.exp 0) := by
  have h : AnalyticOnNhd ℂ (dslope Complex.exp 0) univ := by
    intro z _
    by_cases hz : z = 0
    · subst z
      obtain ⟨p, hp⟩ := analyticAt_cexp (z := (0 : ℂ))
      exact hp.has_fpower_series_dslope_fslope.analyticAt
    · have hDiv : AnalyticAt ℂ (fun w : ℂ => (Complex.exp w - 1) / w) z :=
        (analyticAt_cexp.sub analyticAt_const).div analyticAt_id hz
      apply hDiv.congr
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [dslope_of_ne _ hw, slope_def_field, sub_zero, Complex.exp_zero]
  exact h.restrictScalars.contDiff

/-- The exponential difference quotient extends continuously into Schwartz space. -/
def SchwartzCompactExponentialStatement : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (Φ : 𝓢(E, ℂ)) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ x ∉ S, Φ x = 0) (z : ℂ),
    let f := exponentialTest b hb Φ S hS hSupport
    ∃ V : ℂ → 𝓢(E, ℂ), Continuous V ∧ (∀ r, f (z + r) - f z = r • V r) ∧
      ∀ x, V 0 x = b x * f z x

theorem schwartzCompactExponential : SchwartzCompactExponentialStatement.{v} := by
  intro E _ _ b hb Φ S hS hSupport z f
  let g (u : ℂ × E) :=
    dslope Complex.exp 0 (u.1 * b u.2) * b u.2 * Complex.exp (z * b u.2) * Φ u.2
  have hSmoothB : ContDiff ℝ ∞ (fun u : ℂ × E => b u.2) := hb.comp contDiff_snd
  have hSmooth : ContDiff ℝ ∞ g :=
    (((contDiff_expDividedDifference.comp (contDiff_fst.mul hSmoothB)).mul hSmoothB).mul
      (contDiff_const.mul hSmoothB).cexp).mul ((Φ.smooth ⊤).comp contDiff_snd)
  have hZero (r : ℂ) (x : E) (hx : x ∉ S) : g (r, x) = 0 := by
    dsimp only [g]
    rw [hSupport x hx, mul_zero]
  let V (r : ℂ) := ofCompactSupport (fun x => g (r, x))
    (hSmooth.comp (contDiff_const.prodMk contDiff_id)) S hS (hZero r)
  have hV : Continuous V := schwartzCompactFamilyContinuity ℂ E ℂ V S hS hZero hSmooth
  refine ⟨V, hV, fun r => ?_, fun x => ?_⟩
  · ext x
    change Complex.exp ((z + r) * b x) * Φ x - Complex.exp (z * b x) * Φ x =
      r * (dslope Complex.exp 0 (r * b x) * b x * Complex.exp (z * b x) * Φ x)
    have hExp : (r * b x) * dslope Complex.exp 0 (r * b x) = Complex.exp (r * b x) - 1 := by
      simpa only [sub_zero, smul_eq_mul, Complex.exp_zero] using
        sub_smul_dslope Complex.exp 0 (r * b x)
    rw [add_mul, Complex.exp_add, show r * (dslope Complex.exp 0 (r * b x) * b x *
        Complex.exp (z * b x) * Φ x) =
      ((r * b x) * dslope Complex.exp 0 (r * b x)) * Complex.exp (z * b x) * Φ x by ring,
      hExp]
    ring
  · change g (0, x) = b x * (Complex.exp (z * b x) * Φ x)
    simp only [g, zero_mul, dslope_same, Complex.deriv_exp, Complex.exp_zero, one_mul]
    ring

end Exponential

end Langlands.Analysis.SchwartzCompactFamilies
