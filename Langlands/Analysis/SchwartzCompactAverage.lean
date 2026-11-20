import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Compact averages of linear pullbacks of Schwartz functions -/

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzCompactAverage

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

end Langlands.Analysis.SchwartzCompactAverage
