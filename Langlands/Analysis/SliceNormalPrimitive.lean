import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Analysis.SliceJetOperators
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # A primitive in one normal coordinate of a flat slice -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function MeasureTheory Set
open scoped ContDiff

namespace Langlands.Analysis

universe uX uY

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Integration from zero to the last coordinate, keeping the other
coordinates fixed. -/
def sliceNormalPrimitive (f : X × Y × ℝ → ℝ) (p : X × Y × ℝ) : ℝ :=
  ∫ t in 0..p.2.2, f (p.1, p.2.1, t)

private theorem sliceNormalPrimitive_smooth_flat {f : X × Y × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sliceNormalPrimitive f) ∧
      ∀ m : ℕ, (∀ x : X, ∀ j < m, iteratedFDeriv ℝ j f (x, (0, 0)) = 0) →
        IsFlatOnZeroSlice m (sliceNormalPrimitive f) := by
  let J := Set.Icc (0 : ℝ) 1
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let μJ := (volume : Measure ℝ).comap (Subtype.val : J → ℝ)
  let : IsFiniteMeasure μJ := ⟨by
    have e := MeasurableEmbedding.subtype_coe (s := J) measurableSet_Icc
    change ((volume : Measure ℝ).comap (Subtype.val : J → ℝ)) univ < ⊤
    rw [e.comap_apply, image_univ, Subtype.range_coe_subtype]
    exact isCompact_Icc.measure_lt_top⟩
  let I : C(J, ℝ) →L[ℝ] ℝ := LinearMap.mkContinuous
    { toFun := fun a => ∫ t, a t ∂μJ
      map_add' := fun a b => integral_add
        (a.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (b.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c a => integral_smul c (fun t => a t) }
    (μJ.real univ)
    (fun a => by
      change ‖∫ t, a t ∂μJ‖ ≤ μJ.real univ * ‖a‖
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall a.norm_coe_le_norm))
  let H (p : (X × Y × ℝ) × ℝ) : ℝ := f (p.1.1, p.1.2.1, p.2 * p.1.2.2)
  have hH : ContDiff ℝ ∞ H :=
    hf.comp (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk (contDiff_snd.mul contDiff_fst.snd.snd)))
  let F (p : X × Y × ℝ) : C(J, ℝ) :=
    ⟨fun t => H (p, t.val),
      hH.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hF : ContDiff ℝ ∞ F := by
    apply contDiffOn_univ.mp
    exact contDiffOn_infty_compactFamily_of_joint
      (⟨Subtype.val, continuous_subtype_val⟩ : C(J, ℝ))
      isOpen_univ isOpen_univ (fun _ => mem_univ _) hH.contDiffOn (fun _ _ _ => rfl)
  let G : X × Y × ℝ → ℝ := I ∘ F
  have hG : ContDiff ℝ ∞ G := I.contDiff.comp hF
  have hprim : sliceNormalPrimitive f = fun p => p.2.2 • G p := by
    funext p
    change (∫ t in 0..p.2.2, f (p.1, p.2.1, t)) =
      p.2.2 • ∫ t : J, f (p.1, p.2.1, t.val * p.2.2) ∂μJ
    rw [show (∫ t : J, f (p.1, p.2.1, t.val * p.2.2) ∂μJ) =
        ∫ t in Icc (0 : ℝ) 1, f (p.1, p.2.1, t * p.2.2) from
      integral_subtype_comap measurableSet_Icc (fun t => f (p.1, p.2.1, t * p.2.2)),
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    simpa only [zero_mul, one_mul] using
      (intervalIntegral.smul_integral_comp_mul_right
        (a := 0) (b := 1) (fun t => f (p.1, p.2.1, t)) p.2.2).symm
  refine ⟨hprim ▸ (contDiff_snd.snd.smul hG), fun m hflat x j hj => ?_⟩
  have hGzero (i : ℕ) (hi : i < m) : iteratedFDeriv ℝ i G (x, (0, 0)) = 0 := by
    change iteratedFDeriv ℝ i (I ∘ F) (x, (0, 0)) = 0
    rw [I.iteratedFDeriv_comp_left hF.contDiffAt (by simp)]
    suffices hFzero : iteratedFDeriv ℝ i F (x, (0, 0)) = 0 by
      rw [hFzero]
      apply ContinuousMultilinearMap.ext
      intro vs
      change I 0 = 0
      exact map_zero I
    apply ContinuousMultilinearMap.ext
    intro vs
    apply ContinuousMap.ext
    intro t
    let L : (X × Y × ℝ) →L[ℝ] X × Y × ℝ :=
      (ContinuousLinearMap.id ℝ X).prodMap
        ((ContinuousLinearMap.id ℝ Y).prodMap (t.val • ContinuousLinearMap.id ℝ ℝ))
    have hL : L (x, (0, 0)) = (x, (0, 0)) := by
      change (x, (0, t.val • (0 : ℝ))) = (x, (0, 0))
      rw [smul_zero]
    let e : C(J, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ t
    have he : e ∘ F = f ∘ L := rfl
    have h := e.iteratedFDeriv_comp_left (x := (x, (0, 0))) hF.contDiffAt
      (show (i : ℕ∞ω) ≤ ∞ by simp)
    rw [he, L.iteratedFDeriv_comp_right hf _ (by simp), hL, hflat x i hi] at h
    have hz := DFunLike.congr_fun h vs
    change (0 : ℝ) = e ((iteratedFDeriv ℝ i F (x, (0, 0))) vs) at hz
    exact hz.symm
  rw [hprim]
  apply norm_le_zero_iff.mp
  refine (norm_iteratedFDeriv_smul_le (contDiff_snd.snd : ContDiff ℝ ∞
    (fun p : X × Y × ℝ => p.2.2)) hG (x, (0, 0)) (by simp)).trans_eq ?_
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hi : i = 0
  · subst i
    rw [norm_iteratedFDeriv_zero, norm_zero, mul_zero, zero_mul]
  · rw [hGzero (j - i) (by omega), norm_zero, mul_zero]

theorem contDiff_sliceNormalPrimitive {f : X × Y × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sliceNormalPrimitive f) :=
  (sliceNormalPrimitive_smooth_flat hf).1

/-- The normal primitive raises the order of vanishing by one. -/
theorem isFlatOnZeroSlice_sliceNormalPrimitive {f : X × Y × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (hflat : ∀ x : X, ∀ j < m, iteratedFDeriv ℝ j f (x, (0, 0)) = 0) :
    IsFlatOnZeroSlice m (sliceNormalPrimitive f) :=
  (sliceNormalPrimitive_smooth_flat hf).2 m hflat

/-- Differentiating the primitive in the last coordinate recovers the original function. -/
theorem fderiv_sliceNormalPrimitive_last {f : X × Y × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : X × Y × ℝ) :
    fderiv ℝ (sliceNormalPrimitive f) p (0, 0, 1) = f p := by
  have hf' := (contDiff_sliceNormalPrimitive hf).contDiffAt.differentiableAt (x := p) (by simp)
  let path (t : ℝ) : X × Y × ℝ := (p.1, p.2.1, t)
  have hpath : HasDerivAt path (0, 0, 1) p.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have h1 := (hf'.hasFDerivAt.comp_hasDerivAt p.2.2 hpath).deriv
  have hc : Continuous (fun t => f (path t)) :=
    hf.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have h2 := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 p.2.2)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).deriv
  exact h1.symm.trans h2

end Langlands.Analysis
