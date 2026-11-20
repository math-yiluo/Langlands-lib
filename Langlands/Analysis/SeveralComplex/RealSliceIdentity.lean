import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # The identity theorem on a totally real slice

A holomorphic function on a polydisc `ball s₀ r ⊆ ℂⁿ` (sup norm) that vanishes on the points
`s₀ + i x` with `x ∈ ℝⁿ` small vanishes on the whole polydisc. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Filter Topology Set

variable {n : ℕ}

/-- The point `s₀ + i x` of `ℂⁿ`, for `x ∈ ℝⁿ`: the slice through `s₀` parallel to `iℝⁿ`. -/
def realSlice (s₀ : Fin n → ℂ) (x : Fin n → ℝ) : Fin n → ℂ :=
  fun j => s₀ j + Complex.I * (x j : ℂ)

theorem realSlice_apply (s₀ : Fin n → ℂ) (x : Fin n → ℝ) (j : Fin n) :
    realSlice s₀ x j = s₀ j + Complex.I * (x j : ℂ) :=
  rfl

theorem norm_realSlice_sub (s₀ : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖realSlice s₀ x - s₀‖ = ‖x‖ := by
  have hj : ∀ j, ‖(realSlice s₀ x - s₀) j‖ = ‖x j‖ := by
    intro j
    simp [realSlice]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    rw [hj]
    exact norm_le_pi_norm x j
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    rw [← hj]
    exact norm_le_pi_norm _ j

theorem dist_realSlice (s₀ : Fin n → ℂ) (x : Fin n → ℝ) :
    dist (realSlice s₀ x) s₀ = ‖x‖ := by
  rw [dist_eq_norm, norm_realSlice_sub]

/-- **Identity theorem on a totally real slice.** If `G` is holomorphic on the polydisc
`ball s₀ r` and `G (s₀ + i x) = 0` for every real `x` with `‖x‖ < δ` (`δ > 0`), then `G`
vanishes on `ball s₀ r`. -/
theorem eqOn_zero_of_realSlice {G : (Fin n → ℂ) → ℂ} {s₀ : Fin n → ℂ} {r δ : ℝ}
    (hG : DifferentiableOn ℂ G (ball s₀ r)) (hδ : 0 < δ)
    (h0 : ∀ x : Fin n → ℝ, ‖x‖ < δ → G (realSlice s₀ x) = 0) :
    EqOn G 0 (ball s₀ r) := by
  classical
  intro s hs
  have hr : 0 < r := pos_of_mem_ball hs
  set δ' := min δ r with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ hr
  -- `P k`: vanishing at points whose coordinates of index `≥ k` lie on the real slice
  let P : ℕ → Prop := fun k => ∀ s ∈ ball s₀ r,
    (∀ j : Fin n, k ≤ j.val → ∃ t : ℝ, |t| < δ' ∧ s j = s₀ j + Complex.I * t) → G s = 0
  have hP0 : P 0 := by
    intro s _ hsl
    choose t ht hst using fun j : Fin n => hsl j (Nat.zero_le _)
    have hx : ‖t‖ < δ := by
      rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · simpa [Subsingleton.elim t 0] using hδ
      · refine (pi_norm_lt_iff hδ).2 fun j => ?_
        rw [Real.norm_eq_abs]
        exact (ht j).trans_le (min_le_left _ _)
    have hs' : s = realSlice s₀ t := funext fun j => hst j
    rw [hs']
    exact h0 t hx
  have hstep : ∀ k, P k → P (k + 1) := by
    intro k hk s hs hsl
    by_cases hkn : k < n
    · let jk : Fin n := ⟨k, hkn⟩
      let φ : ℂ → ℂ := fun z => G (Function.update s jk z)
      have hupd : ∀ z ∈ ball (s₀ jk) r, Function.update s jk z ∈ ball s₀ r := by
        intro z hz
        rw [mem_ball] at hs hz ⊢
        refine (dist_pi_lt_iff hr).2 fun i => ?_
        rcases eq_or_ne i jk with rfl | hi
        · simpa using hz
        · rw [Function.update_of_ne hi]
          exact (dist_le_pi_dist s s₀ i).trans_lt hs
      have hφ : DifferentiableOn ℂ φ (ball (s₀ jk) r) := by
        intro z hz
        have h1 : DifferentiableAt ℂ G (Function.update s jk z) :=
          hG.differentiableAt (isOpen_ball.mem_nhds (hupd z hz))
        exact (h1.comp z (hasFDerivAt_update s z).differentiableAt).differentiableWithinAt
      have hzero : ∀ t : ℝ, |t| < δ' → φ (s₀ jk + Complex.I * t) = 0 := by
        intro t ht
        apply hk
        · apply hupd
          rw [mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
          exact ht.trans_le (min_le_right _ _)
        · intro j hj
          rcases eq_or_ne j jk with rfl | hne
          · exact ⟨t, ht, by simp⟩
          · have hj' : k + 1 ≤ j.val := by
              have : j.val ≠ k := fun h => hne (Fin.ext h)
              omega
            obtain ⟨t', ht', hst'⟩ := hsl j hj'
            exact ⟨t', ht', by rw [Function.update_of_ne hne]; exact hst'⟩
      have hfreq : ∃ᶠ z in 𝓝[≠] (s₀ jk), φ z = 0 := by
        let zseq : ℕ → ℂ := fun i => s₀ jk + Complex.I * ((δ' / ((i : ℝ) + 2) : ℝ) : ℂ)
        have hpos : ∀ i : ℕ, 0 < δ' / ((i : ℝ) + 2) := fun i => by positivity
        have hlim : Tendsto zseq atTop (𝓝[≠] (s₀ jk)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun i => ?_⟩
          · have h1 : Tendsto (fun i : ℕ => δ' / ((i : ℝ) + 2)) atTop (𝓝 0) :=
              tendsto_const_nhds.div_atTop
                (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
            have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul Complex.I
            have h3 := h2.const_add (s₀ jk)
            rw [Complex.ofReal_zero, mul_zero, add_zero] at h3
            exact h3
          · simp only [mem_compl_iff, mem_singleton_iff, zseq, add_eq_left, mul_eq_zero,
              Complex.I_ne_zero, Complex.ofReal_eq_zero, false_or]
            exact (hpos i).ne'
        refine hlim.frequently (Frequently.of_forall fun i => hzero _ ?_)
        rw [abs_of_pos (hpos i), div_lt_iff₀ (by positivity)]
        nlinarith [hδ'pos, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      have hall := (hφ.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball _ _).isPreconnected (mem_ball_self hr) hfreq
      have hsjk : s jk ∈ ball (s₀ jk) r := by
        rw [mem_ball] at hs ⊢
        exact (dist_le_pi_dist s s₀ jk).trans_lt hs
      have := hall hsjk
      simpa [φ] using this
    · apply hk s hs
      intro j hj
      exact absurd (lt_of_le_of_lt hj j.isLt) hkn
  have hPall : ∀ k, P k := by
    intro k
    induction k with
    | zero => exact hP0
    | succ k ih => exact hstep k ih
  exact hPall n s hs fun j hj => absurd j.isLt (not_lt.2 hj)

end Langlands.Analysis.SeveralComplex
