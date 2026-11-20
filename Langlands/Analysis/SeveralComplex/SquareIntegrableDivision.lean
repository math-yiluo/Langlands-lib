import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! # Square-integrable quotients by real polynomials in one variable

If `f` is holomorphic on a disc around `0` and `t ↦ f t / q t` is square integrable on a real
interval `(-T, T)` that contains all the (real) roots of `q = c ∏ (w - τ i)`, then `q` divides
`f`: `f = q φ` with `φ` holomorphic on the disc. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open MeasureTheory Metric Filter Topology Set

/-- If `t ↦ g t / ((t - a) p t)` is square integrable near the real point `a`, `g` and `p` are
continuous at `a` and `p t ≠ 0` for almost every real `t`, then `g a = 0`. -/
theorem eq_zero_of_integrableOn_sq_div {g p : ℂ → ℂ} {a T : ℝ} (ha : |a| < T)
    (hg : ContinuousAt g a) (hp : ContinuousAt p a) (hp0 : ∀ᵐ t : ℝ, p t ≠ 0)
    (hint : IntegrableOn (fun t : ℝ => ‖g t / (((t : ℂ) - a) * p t)‖ ^ 2) (Ioo (-T) T)) :
    g a = 0 := by
  by_contra hga
  set ε := ‖g a‖ / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; exact half_pos (norm_pos_iff.2 hga)
  obtain ⟨δ₁, hδ₁, hδ₁g⟩ := Metric.continuousAt_iff.1 hg ε hεpos
  obtain ⟨δ₂, hδ₂, hδ₂p⟩ := Metric.continuousAt_iff.1 hp 1 one_pos
  set M := ‖p a‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  set δ := min (min δ₁ δ₂) (min 1 (T - |a|)) with hδ
  have hδpos : 0 < δ := by
    simp only [hδ, lt_min_iff]
    exact ⟨⟨hδ₁, hδ₂⟩, one_pos, by linarith⟩
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hsub : Ioo (a - δ) (a + δ) ⊆ Ioo (-T) T := by
    have : δ ≤ T - |a| := (min_le_right _ _).trans (min_le_right _ _)
    intro t ht
    constructor
    · linarith [ht.1, neg_abs_le a]
    · linarith [ht.2, le_abs_self a]
  -- the lower bound `|t - a|⁻¹ ≤ K ‖g t / ((t - a) p t)‖²` near `a`
  set K := M ^ 2 / ε ^ 2 with hK
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioo (a - δ) (a + δ))),
      ‖(t - a)⁻¹‖ ≤ K * ‖g t / (((t : ℂ) - a) * p t)‖ ^ 2 := by
    have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Ioo (a - δ) (a + δ))), t ≠ a :=
      ae_restrict_of_ae (Measure.ae_ne volume a)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hp0, hne] with t ht hpt hta
    have hdist : dist (t : ℂ) (a : ℂ) < δ := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_lt_iff]
      constructor <;> linarith [ht.1, ht.2]
    have hgt : ε ≤ ‖g t‖ := by
      have h1 := hδ₁g (hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le (g a) (g a - g t)
      rw [sub_sub_cancel, norm_sub_rev] at h2
      linarith
    have hpt' : ‖p t‖ ≤ M := by
      have h1 := hδ₂p (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      rw [dist_eq_norm] at h1
      have h2 := norm_le_insert' (p t) (p a)
      rw [hM]
      linarith [norm_sub_rev (p t) (p a)]
    have hta' : 0 < |t - a| := abs_pos.2 (sub_ne_zero.2 hta)
    have hta1 : |t - a| < 1 := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith [ht.1, ht.2]
    have hnorm : ‖g t / (((t : ℂ) - a) * p t)‖ = ‖g t‖ / (|t - a| * ‖p t‖) := by
      rw [norm_div, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < ‖p t‖ := norm_pos_iff.2 hpt
    rw [hnorm, norm_inv, Real.norm_eq_abs, hK]
    have key : ε / (|t - a| * M) ≤ ‖g t‖ / (|t - a| * ‖p t‖) := by
      apply div_le_div₀ (norm_nonneg _) hgt (by positivity)
      exact mul_le_mul_of_nonneg_left hpt' hta'.le
    have key2 : (ε / (|t - a| * M)) ^ 2 ≤ (‖g t‖ / (|t - a| * ‖p t‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) key 2
    calc |t - a|⁻¹ ≤ (|t - a| ^ 2)⁻¹ := by
          rw [inv_le_inv₀ hta' (by positivity)]
          nlinarith
      _ = M ^ 2 / ε ^ 2 * (ε / (|t - a| * M)) ^ 2 := by
          field_simp
      _ ≤ M ^ 2 / ε ^ 2 * (‖g t‖ / (|t - a| * ‖p t‖)) ^ 2 := by
          gcongr
  have hint' : IntegrableOn (fun t : ℝ => (t - a)⁻¹) (Ioo (a - δ) (a + δ)) := by
    refine Integrable.mono' ((hint.mono_set hsub).const_mul K) ?_ hbound
    exact ((measurable_id.sub_const a).inv).aestronglyMeasurable
  have hII : IntervalIntegrable (fun t : ℝ => (t - a)⁻¹) volume (a - δ) (a + δ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    exact hint'
  rcases intervalIntegrable_sub_inv_iff.1 hII with h | h
  · linarith
  · apply h
    rw [Set.uIcc_of_le (by linarith)]
    constructor <;> linarith

/-- **Division in one variable.** Let `f` be holomorphic on `ball 0 R`, `c ≠ 0`, and let the
real numbers `τ i` (`i ∈ s`) satisfy `|τ i| < T ≤ R`. If `t ↦ f t / (c ∏ (t - τ i))` is square
integrable on `(-T, T)`, then `f = c ∏ (w - τ i) · φ` on `ball 0 R` with `φ` holomorphic. -/
theorem exists_eq_mul_prod_of_integrableOn {ι : Type*} (s : Finset ι) (τ : ι → ℝ) {c : ℂ}
    (hc : c ≠ 0) {R T : ℝ} (hTR : T ≤ R) (hτ : ∀ i ∈ s, |τ i| < T) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hint : IntegrableOn
      (fun t : ℝ => ‖f t / (c * ∏ i ∈ s, ((t : ℂ) - τ i))‖ ^ 2) (Ioo (-T) T)) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball 0 R) ∧
      ∀ w ∈ ball (0 : ℂ) R, f w = c * (∏ i ∈ s, (w - τ i)) * φ w := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    refine ⟨fun w => f w / c, hf.div_const c, fun w _ => ?_⟩
    simp only [Finset.prod_empty, mul_one]
    field_simp
  | insert i s hi ih =>
    have hτi : |τ i| < T := hτ i (Finset.mem_insert_self i s)
    have hτs : ∀ j ∈ s, |τ j| < T := fun j hj => hτ j (Finset.mem_insert_of_mem hj)
    have hτR : (τ i : ℂ) ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hfc : ContinuousAt f (τ i) := (hf.differentiableAt (isOpen_ball.mem_nhds hτR)).continuousAt
    -- the polynomial factor of the other roots
    let p : ℂ → ℂ := fun w => c * ∏ j ∈ s, (w - τ j)
    have hpc : Continuous p := by
      simp only [p]
      fun_prop
    have hp0 : ∀ᵐ t : ℝ, p t ≠ 0 := by
      have hfin : (⋃ j ∈ s, ({τ j} : Set ℝ)).Countable :=
        (s.countable_toSet.biUnion fun j _ => countable_singleton (τ j))
      filter_upwards [hfin.ae_notMem volume] with t ht
      simp only [p, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
      refine ⟨hc, fun j hj hzero => ht ?_⟩
      have : t = τ j := by exact_mod_cast sub_eq_zero.1 hzero
      exact mem_biUnion hj (mem_singleton_iff.2 this)
    have hq : ∀ t : ℝ, c * ∏ j ∈ insert i s, ((t : ℂ) - τ j) = ((t : ℂ) - τ i) * p t := by
      intro t
      rw [Finset.prod_insert hi]
      ring
    have hint1 : IntegrableOn (fun t : ℝ => ‖f t / (((t : ℂ) - τ i) * p t)‖ ^ 2) (Ioo (-T) T) := by
      refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioo
      simp only [hq]
    -- `f` vanishes at the root `τ i`
    have hfτ : f (τ i) = 0 :=
      eq_zero_of_integrableOn_sq_div hτi hfc hpc.continuousAt hp0 hint1
    -- divide by `w - τ i`
    let f₁ := dslope f (τ i)
    have hf₁ : DifferentiableOn ℂ f₁ (ball 0 R) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hτR)).2 hf
    have hff₁ : ∀ w, f w = (w - τ i) * f₁ w := by
      intro w
      have := sub_smul_dslope f (τ i : ℂ) w
      rw [hfτ, sub_zero, smul_eq_mul] at this
      exact this.symm
    have hint₁ : IntegrableOn
        (fun t : ℝ => ‖f₁ t / (c * ∏ j ∈ s, ((t : ℂ) - τ j))‖ ^ 2) (Ioo (-T) T) := by
      refine hint1.congr_fun_ae ?_
      filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (τ i))] with t ht
      have hne : (t : ℂ) - τ i ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ht
      simp only [p]
      rw [hff₁ t, mul_div_mul_left _ _ hne]
    obtain ⟨φ, hφ, hfφ⟩ := ih hτs hf₁ hint₁
    refine ⟨φ, hφ, fun w hw => ?_⟩
    rw [hff₁ w, hfφ w hw, Finset.prod_insert hi]
    ring

end Langlands.Analysis.SeveralComplex
