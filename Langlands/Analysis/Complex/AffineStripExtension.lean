import Langlands.Analysis.Complex.EntireStripExtension

/-! # Holomorphic limits from pairs of vertical lines along affine parameter diagonals -/

noncomputable section

open Filter Set
open scoped Topology
open Langlands.LocalFactor.Archimedean (HasStripExponentialGrowth)

set_option autoImplicit false

namespace Langlands.Analysis

private theorem stripGrowth_sub {f g : ℂ → ℂ} (hf : HasStripExponentialGrowth f)
    (hg : HasStripExponentialGrowth g) : HasStripExponentialGrowth (f - g) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf a b
  obtain ⟨D, L, U, hD, hL, hg⟩ := hg a b
  refine ⟨C + D, max K L, max T U, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro z ha hb hz
  rw [Pi.sub_apply, add_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (hf z ha hb ((le_max_left _ _).trans hz)).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hg z ha hb ((le_max_right _ _).trans hz)).trans ?_
    gcongr
    exact le_max_right _ _

/-- Boundary estimates on the lines `(v + s, s)` give a locally uniform limit on
`ℂ × ℂ` and a strip growth bound with the first coordinate held fixed. -/
def AffineStripExtensionStatement : Prop :=
  ∀ (F : ℕ → ℂ × ℂ → ℂ), (∀ j, Differentiable ℂ (F j)) →
    (∀ (j : ℕ) (u : ℂ), HasStripExponentialGrowth (fun s => F j (u, s))) →
    (∀ (j : ℕ) (v : ℂ), HasStripExponentialGrowth (fun s => F j (v + s, s))) →
    (∀ R a b : ℝ, 0 ≤ R → a ≤ b → ∃ a₀ b₀ K L : ℝ, a₀ < a ∧ b < b₀ ∧ 0 ≤ L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
        ∀ v s : ℂ, |v.re| ≤ R → s.re = a₀ ∨ s.re = b₀ →
          ‖F i (v + s, s) - F j (v + s, s)‖ ≤ ε * Real.exp (K * |s.im| + L * |v.im|)) →
    ∃ f : ℂ × ℂ → ℂ, TendstoLocallyUniformly F f atTop ∧
      (∀ γ : ℂ → ℂ × ℂ, Differentiable ℂ γ → Differentiable ℂ (f ∘ γ)) ∧
      ∀ u : ℂ, HasStripExponentialGrowth (fun s => f (u, s))

set_option maxHeartbeats 500000 in
theorem affineStripExtension : AffineStripExtensionStatement := by
  intro F hF hGrowth hAffine hLines
  have hStrips (R a b : ℝ) (hR : 0 ≤ R) (hab : a ≤ b) :
      ∃ A B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ v s : ℂ, |v.re| ≤ R → a ≤ s.re → s.re ≤ b →
          ‖F i (v + s, s) - F j (v + s, s)‖ ≤
            ε * Real.exp (A + B * |s.im| + L * |v.im|) := by
    obtain ⟨a₀, b₀, K, L, ha, hb, hL, h⟩ := hLines R a b hR hab
    let A := (max |a₀| |b₀|) ^ 2 + K ^ 2 / 4
    let B := 1 + K ^ 2 / 4
    refine ⟨A, B, L, by positivity, hL, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun i j hi hj v s hv hs₁ hs₂ => ?_⟩
    let g : ℂ → ℂ × ℂ := fun w => (v + w, w)
    have hg : Differentiable ℂ g := Differentiable.prodMk
      ((differentiable_const v).add differentiable_id) differentiable_id
    let U (w : ℂ) : ℂ := F i (g w) - F j (g w)
    have hU : Differentiable ℂ U := ((hF i).comp hg).sub ((hF j).comp hg)
    have hUg : HasStripExponentialGrowth U := stripGrowth_sub (hAffine i v) (hAffine j v)
    have hboundary (w : ℂ) (hw : w.re = a₀ ∨ w.re = b₀) :
        ‖U w‖ ≤ (ε * Real.exp (L * |v.im|)) * Real.exp (K * |w.im|) := by
      have h' := hN i j hi hj v w hv hw
      change ‖U w‖ ≤ _ at h'
      simpa only [Real.exp_add, mul_left_comm, mul_assoc, mul_comm] using h'
    have h' := norm_le_of_exp_bounds_on_vertical_lines hU hUg (ha.trans_le (hab.trans hb.le))
      (show 0 ≤ ε * Real.exp (L * |v.im|) by positivity) hboundary
      (ha.le.trans hs₁) (hs₂.trans hb.le)
    change ‖U s‖ ≤ ε * Real.exp (A + B * |s.im| + L * |v.im|)
    change ‖U s‖ ≤ (ε * Real.exp (L * |v.im|)) * Real.exp (A + B * |s.im|) at h'
    rw [mul_assoc, ← Real.exp_add, add_comm (L * |v.im|)] at h'
    exact h'
  have hBox (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ p : ℂ × ℂ, ‖p‖ ≤ R →
        ‖F i p - F j p‖ ≤ ε := by
    obtain ⟨A, B, L, hB, hL, h⟩ := hStrips (2 * R) (-R) R (by linarith) (by linarith)
    let M := Real.exp (A + B * R + L * (2 * R))
    have hM : 0 < M := Real.exp_pos _
    obtain ⟨N, hN⟩ := h (ε / M) (div_pos hε hM)
    refine ⟨N, fun i j hi hj p hp => ?_⟩
    have hr₁ : ‖p.1‖ ≤ R := (norm_fst_le p).trans hp
    have hr₂ : ‖p.2‖ ≤ R := (norm_snd_le p).trans hp
    have hsub : ‖p.1 - p.2‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    obtain ⟨hl, hr⟩ := abs_le.mp ((Complex.abs_re_le_norm p.2).trans hr₂)
    have hb := hN i j hi hj (p.1 - p.2) p.2 ((Complex.abs_re_le_norm _).trans hsub) hl hr
    rw [sub_add_cancel] at hb
    refine hb.trans ?_
    have him₁ := (Complex.abs_im_le_norm (p.1 - p.2)).trans hsub
    have him₂ := (Complex.abs_im_le_norm p.2).trans hr₂
    calc
      _ ≤ (ε / M) * M := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by gcongr)) (div_nonneg hε.le hM.le)
      _ = ε := div_mul_cancel₀ _ hM.ne'
  have hpt (p : ℂ × ℂ) : CauchySeq (fun j => F j p) := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hBox ‖p‖ (norm_nonneg _) (ε / 2) (half_pos hε)
    exact ⟨N, fun i hi j hj => by
      rw [dist_eq_norm]
      exact (hN i j hi hj p le_rfl).trans_lt (half_lt_self hε)⟩
  choose f hf using fun p => cauchySeq_tendsto_of_complete (hpt p)
  have hlim : TendstoLocallyUniformly F f atTop := by
    refine tendstoLocallyUniformly_iff_forall_isCompact.mpr fun T hT =>
      Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨R, hR⟩ := hT.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨N, hN⟩ := hBox (max R 0) (le_max_right _ _) (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with i hi p hp
    have hd : ‖F i p - f p‖ ≤ ε / 2 := by
      apply le_of_tendsto (((tendsto_const_nhds (x := F i p)).sub (hf p)).norm)
      filter_upwards [eventually_ge_atTop N] with j hj
      exact hN i j hi hj p ((hR p hp).trans (le_max_left _ _))
    rw [dist_comm, dist_eq_norm]
    exact hd.trans_lt (half_lt_self hε)
  refine ⟨f, hlim, ?_, ?_⟩
  · intro γ hγ
    exact differentiableOn_univ.mp ((hlim.comp γ hγ.continuous).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun j => ((hF j).comp hγ).differentiableOn) isOpen_univ)
  · intro u a b
    let R := |u.re| + max |a| |b|
    have hR : 0 ≤ R := add_nonneg (abs_nonneg _) ((abs_nonneg _).trans (le_max_left _ _))
    obtain ⟨A, B, L, hB, hL, h⟩ := hStrips R (min a b) b hR (min_le_right _ _)
    obtain ⟨N, hN⟩ := h 1 one_pos
    obtain ⟨C, K, T, hC, hK, hFn⟩ := hGrowth N u a b
    let M := Real.exp (A + L * |u.im|)
    refine ⟨M + C, max (B + L) K, T, add_nonneg (Real.exp_pos _).le hC,
      (add_nonneg hB hL).trans (le_max_left _ _), ?_⟩
    intro s ha hb hs
    have hab : |s.re| ≤ max |a| |b| := by
      apply abs_le.mpr
      exact ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans ha),
        hb.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    have hvr : |(u - s).re| ≤ R := by
      rw [Complex.sub_re]
      exact (abs_sub _ _).trans (add_le_add (le_refl _) hab)
    have hvi : |(u - s).im| ≤ |u.im| + |s.im| := by
      rw [Complex.sub_im]
      exact abs_sub _ _
    have hdiff : ‖f (u, s) - F N (u, s)‖ ≤ M * Real.exp ((B + L) * |s.im|) := by
      apply le_of_tendsto (((hf (u, s)).sub tendsto_const_nhds).norm)
      filter_upwards [eventually_ge_atTop N] with j hj
      have h' := hN j N hj le_rfl (u - s) s hvr ((min_le_left _ _).trans ha) hb
      rw [sub_add_cancel, one_mul] at h'
      refine h'.trans ?_
      dsimp only [M]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left hvi hL]
    calc
      ‖f (u, s)‖ = ‖f (u, s) - F N (u, s) + F N (u, s)‖ := by rw [sub_add_cancel]
      _ ≤ M * Real.exp ((B + L) * |s.im|) + C * Real.exp (K * |s.im|) :=
        (norm_add_le _ _).trans (add_le_add hdiff (hFn s ha hb hs))
      _ ≤ _ := by
        rw [add_mul M C]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
            (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))) hC

end Langlands.Analysis
