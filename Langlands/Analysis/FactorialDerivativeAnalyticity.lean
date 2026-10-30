import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Factorial derivative bounds imply real analyticity -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff Nat

namespace Langlands.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Along a segment inside a ball of smoothness, the one-variable iterated derivative of
`t ↦ f (x + t • y)` is the iterated Frechet derivative of `f` evaluated on `y, …, y`. -/
theorem iteratedDeriv_comp_line {f : E → F} {x y : E} {r : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x r)) {t : ℝ} (ht : ‖t • y‖ < r) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => f (x + s • y)) t =
      iteratedFDeriv ℝ k f (x + t • y) (fun _ => y) := by
  set L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight y with hL
  have hLapp : ∀ s : ℝ, L s = s • y := fun s => by simp [hL]
  set g : E → F := fun z => f (x + z) with hg
  have hgs : ContDiffOn ℝ ∞ g (Metric.ball 0 r) := by
    have : MapsTo (fun z : E => x + z) (Metric.ball 0 r) (Metric.ball x r) := by
      intro z hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact hf.comp (contDiff_const.add contDiff_id).contDiffOn this
  have hcomp : (fun s : ℝ => f (x + s • y)) = g ∘ L := by
    funext s
    simp [hg, hLapp]
  have hopen : IsOpen (Metric.ball (0 : E) r) := Metric.isOpen_ball
  have hpre : IsOpen (L ⁻¹' Metric.ball (0 : E) r) := hopen.preimage L.continuous
  have htmem : t ∈ L ⁻¹' Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_eq_norm, hLapp] using ht
  have hLt : L t ∈ Metric.ball (0 : E) r := htmem
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
    ← iteratedFDerivWithin_of_isOpen k hpre htmem,
    L.iteratedFDerivWithin_comp_right hgs hopen.uniqueDiffOn hpre.uniqueDiffOn hLt
      (by exact_mod_cast le_top),
    iteratedFDerivWithin_of_isOpen k hopen hLt]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLapp, one_smul]
  rw [hg, iteratedFDeriv_comp_add_left]

/-- The real Taylor series of `f` at `x`: its `n`-th term is `(n!)⁻¹ • D^n f(x)`, built from the
actual iterated Frechet derivatives of `f`. -/
def realTaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun n => ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n f x

theorem realTaylorSeries_apply (f : E → F) (x : E) (n : ℕ) :
    realTaylorSeries f x n = ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n f x :=
  rfl

/-- **Factorial derivative bounds give a convergent Taylor expansion.**  If `f` is smooth on a
ball around `x` and all iterated Frechet derivatives on that ball satisfy
`‖D^k f‖ ≤ C * M ^ k * k!`, then the Taylor series of `f` at `x` converges to `f` on the ball of
radius `min (r / 2) (1 / (2 * (|M| + 1)))`. -/
theorem hasFPowerSeriesOnBall_realTaylorSeries_of_iteratedFDeriv_le_factorial {f : E → F}
    {x : E} {r C M : ℝ} (hr : 0 < r) (hf : ContDiffOn ℝ ∞ f (Metric.ball x r))
    (hbound : ∀ y ∈ Metric.ball x r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k !) :
    HasFPowerSeriesOnBall f (realTaylorSeries f x) x
      (ENNReal.ofReal (min (r / 2) (1 / (2 * (|M| + 1))))) := by
  have hC : 0 ≤ C := by
    have h := hbound x (Metric.mem_ball_self hr) 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at h
    exact (norm_nonneg _).trans h
  set M₁ : ℝ := |M| + 1 with hM₁
  have hM₁pos : 0 < M₁ := by positivity
  -- Bounds with the positive constant `M₁`.
  have hbound₁ : ∀ y ∈ Metric.ball x r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M₁ ^ k * k ! := by
    intro y hy k
    refine (hbound y hy k).trans ?_
    have h1 : M ^ k ≤ M₁ ^ k := by
      calc M ^ k ≤ |M ^ k| := le_abs_self _
        _ = |M| ^ k := abs_pow M k
        _ ≤ M₁ ^ k := pow_le_pow_left₀ (abs_nonneg M) (by rw [hM₁]; linarith) k
    have h2 : (0 : ℝ) ≤ k ! := by positivity
    gcongr
  -- The radius of the Taylor ball.
  set ρ : ℝ := min (r / 2) (1 / (2 * M₁)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρM : M₁ * ρ ≤ 1 / 2 := by
    have : ρ ≤ 1 / (2 * M₁) := min_le_right _ _
    calc M₁ * ρ ≤ M₁ * (1 / (2 * M₁)) := by gcongr
      _ = 1 / 2 := by field_simp
  -- The Taylor series at `x`.
  set p : FormalMultilinearSeries ℝ E F := realTaylorSeries f x with hp
  have hpnorm : ∀ n : ℕ, ‖p n‖ ≤ C * M₁ ^ n := by
    intro n
    have hfac : (0 : ℝ) < n ! := by positivity
    calc ‖p n‖ = (n ! : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n f x‖ := by
          rw [hp, realTaylorSeries_apply, norm_smul, norm_inv, Real.norm_natCast]
      _ ≤ (n ! : ℝ)⁻¹ * (C * M₁ ^ n * n !) := by
          gcongr
          exact hbound₁ x (Metric.mem_ball_self hr) n
      _ = C * M₁ ^ n * ((n ! : ℝ)⁻¹ * n !) := by ring
      _ = C * M₁ ^ n := by rw [inv_mul_cancel₀ hfac.ne', mul_one]
  -- Pointwise bound on a term of the series.
  have hterm : ∀ (n : ℕ) (y : E), ‖p n (fun _ => y)‖ ≤ C * (M₁ * ‖y‖) ^ n := by
    intro n y
    calc ‖p n (fun _ => y)‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := (p n).le_opNorm _
      _ = ‖p n‖ * ‖y‖ ^ n := by simp
      _ ≤ C * M₁ ^ n * ‖y‖ ^ n := by gcongr; exact hpnorm n
      _ = C * (M₁ * ‖y‖) ^ n := by rw [mul_pow, mul_assoc]
  set ρ' : NNReal := ⟨ρ, hρpos.le⟩ with hρ'
  have hρ'ρ : (ρ' : ℝ) = ρ := rfl
  have hofReal : ENNReal.ofReal ρ = (ρ' : ENNReal) := by
    show ((ρ.toNNReal : NNReal) : ENNReal) = ρ'
    rw [Real.toNNReal_of_nonneg hρpos.le]
    rfl
  rw [hofReal]
  refine
    { r_le := ?_
      r_pos := ENNReal.coe_pos.2 (NNReal.coe_pos.1 hρpos)
      hasSum := ?_ }
  · -- The radius is at least `ρ`.
    refine p.le_radius_of_bound C (fun n => ?_)
    rw [hρ'ρ]
    calc ‖p n‖ * ρ ^ n ≤ C * M₁ ^ n * ρ ^ n := by
          gcongr; exact hpnorm n
      _ = C * (M₁ * ρ) ^ n := by rw [mul_pow, mul_assoc]
      _ ≤ C * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) (hρM.trans (by norm_num))
      _ = C := mul_one C
  · intro y hy
    have hyρ : ‖y‖ < ρ := by
      have h1 : ‖y‖₊ < ρ' := enorm_lt_coe.1 (mem_eball_zero_iff.1 hy)
      have h2 : (‖y‖₊ : ℝ) < (ρ' : ℝ) := NNReal.coe_lt_coe.2 h1
      rwa [coe_nnnorm, hρ'ρ] at h2
    set q : ℝ := M₁ * ‖y‖ with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      calc q ≤ M₁ * ρ := by rw [hq]; gcongr
        _ ≤ 1 / 2 := hρM
        _ < 1 := by norm_num
    -- Summability of the norms.
    have hsum : Summable (fun n => ‖p n (fun _ => y)‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hterm n y) ?_
      exact (summable_geometric_of_lt_one hq0 hq1).mul_left C
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    -- The function along the segment.
    set g : ℝ → F := fun s => f (x + s • y) with hg
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • y‖ < r := by
      intro s hs
      calc ‖s • y‖ = |s| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖y‖ := by
            gcongr
            rw [abs_of_nonneg hs.1]; exact hs.2
        _ < r := by linarith
    -- `g` is smooth on an open set containing `[0, 1]`.
    set T : Set ℝ := {s : ℝ | ‖s • y‖ < r} with hT
    have hTopen : IsOpen T :=
      isOpen_lt (continuous_id.smul continuous_const).norm continuous_const
    have hgT : ContDiffOn ℝ ∞ g T := by
      have hmaps : MapsTo (fun s : ℝ => x + s • y) T (Metric.ball x r) := by
        intro s hs
        have hs' : ‖s • y‖ < r := hs
        simpa [Metric.mem_ball, dist_eq_norm] using hs'
      exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hmaps
    have hIccT : Icc (0 : ℝ) 1 ⊆ T := fun s hs => hseg s hs
    have hderiv : ∀ (k : ℕ), ∀ s ∈ Icc (0 : ℝ) 1,
        iteratedDerivWithin k g (Icc 0 1) s = iteratedFDeriv ℝ k f (x + s • y) (fun _ => y) := by
      intro k s hs
      have hat : ContDiffAt ℝ k g s :=
        ((hgT.contDiffAt (hTopen.mem_nhds (hIccT hs))).of_le (by exact_mod_cast le_top))
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) hat hs]
      exact iteratedDeriv_comp_line hf (hseg s hs) k
    -- Taylor polynomial equals the partial sums.
    have htaylor : ∀ N : ℕ, taylorWithinEval g N (Icc 0 1) 0 1 =
        ∑ i ∈ Finset.range (N + 1), p i (fun _ => y) := by
      intro N
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hderiv k 0 ⟨le_rfl, zero_le_one⟩]
      simp [hp, realTaylorSeries_apply]
    -- The remainder bound.
    have hrem : ∀ N : ℕ, ‖f (x + y) - ∑ i ∈ Finset.range (N + 1), p i (fun _ => y)‖ ≤
        C * ((N + 1 : ℕ) * q ^ (N + 1)) := by
      intro N
      have hcd : ContDiffOn ℝ (N + 1) g (Icc 0 1) :=
        (hgT.mono hIccT).of_le (by exact_mod_cast le_top)
      have hB : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (N + 1) g (Icc 0 1) s‖ ≤
          C * M₁ ^ (N + 1) * (N + 1)! * ‖y‖ ^ (N + 1) := by
        intro s hs
        rw [hderiv (N + 1) s hs]
        have hmem : x + s • y ∈ Metric.ball x r := by
          simpa [Metric.mem_ball, dist_eq_norm] using hseg s hs
        calc ‖iteratedFDeriv ℝ (N + 1) f (x + s • y) (fun _ => y)‖
            ≤ ‖iteratedFDeriv ℝ (N + 1) f (x + s • y)‖ * ∏ _i : Fin (N + 1), ‖y‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ (N + 1) f (x + s • y)‖ * ‖y‖ ^ (N + 1) := by simp
          _ ≤ C * M₁ ^ (N + 1) * (N + 1)! * ‖y‖ ^ (N + 1) := by
              gcongr
              exact hbound₁ _ hmem (N + 1)
      have h := taylor_mean_remainder_bound zero_le_one hcd ⟨zero_le_one, le_rfl⟩ hB
      rw [htaylor N] at h
      have hg1 : g 1 = f (x + y) := by simp [hg]
      rw [hg1] at h
      refine h.trans (le_of_eq ?_)
      have hfac : (N ! : ℝ) ≠ 0 := by positivity
      rw [sub_zero, one_pow, mul_one, Nat.factorial_succ, Nat.cast_mul, hq, mul_pow,
        div_eq_iff hfac]
      push_cast
      ring
    -- Convergence of the partial sums.
    rw [← tendsto_add_atTop_iff_nat 1]
    have hlim : Tendsto (fun N : ℕ => C * ((N + 1 : ℕ) * q ^ (N + 1))) atTop (𝓝 0) := by
      have h0 := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
      have h1 := (tendsto_add_atTop_iff_nat 1).2 h0
      simpa using h1.const_mul C
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
    rw [norm_sub_rev]
    exact hrem N

/-- **Factorial derivative bounds give analyticity.**  If `f` is smooth on a ball around `x`
and all iterated Frechet derivatives on that ball satisfy `‖D^k f‖ ≤ C * M ^ k * k!`, then
`f` is real analytic at `x`. -/
theorem analyticAt_of_iteratedFDeriv_le_factorial {f : E → F} {x : E} {r C M : ℝ}
    (hr : 0 < r) (hf : ContDiffOn ℝ ∞ f (Metric.ball x r))
    (hbound : ∀ y ∈ Metric.ball x r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k !) :
    AnalyticAt ℝ f x :=
  ⟨_, _, hasFPowerSeriesOnBall_realTaylorSeries_of_iteratedFDeriv_le_factorial hr hf hbound⟩

/-- Local factorial derivative bounds near every point of an open set give analyticity on a
neighborhood of every point of the set. -/
theorem analyticOnNhd_of_iteratedFDeriv_le_factorial {f : E → F} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S)
    (hbound : ∀ x ∈ S, ∃ C M : ℝ, ∀ᶠ y in 𝓝 x, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k !) :
    AnalyticOnNhd ℝ f S := by
  intro x hx
  obtain ⟨C, M, hev⟩ := hbound x hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hev (hS.mem_nhds hx))
  exact analyticAt_of_iteratedFDeriv_le_factorial hr (hf.mono fun y hy => (hball hy).2)
    (fun y hy k => (hball hy).1 k)

/-- A continuous multilinear map on a space with a finite basis is controlled by its values on
basis words: if `‖T (b ∘ w)‖ ≤ B` for every word `w`, then
`‖T‖ ≤ B * (card ι * ‖b.equivFunL‖) ^ k`. -/
theorem norm_le_of_basis_word_le {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ w : Fin k → ι, ‖T (fun j => b (w j))‖ ≤ B) :
    ‖T‖ ≤ B * (Fintype.card ι * ‖(b.equivFunL : E →L[ℝ] ι → ℝ)‖) ^ k := by
  classical
  set A : ℝ := ‖(b.equivFunL : E →L[ℝ] ι → ℝ)‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  refine T.opNorm_le_bound (by positivity) (fun v => ?_)
  have hcoord : ∀ (i : ι) (z : E), |b.equivFun z i| ≤ A * ‖z‖ := by
    intro i z
    calc |b.equivFun z i| = ‖(b.equivFunL : E →L[ℝ] ι → ℝ) z i‖ := by
          rw [Real.norm_eq_abs]; rfl
      _ ≤ ‖(b.equivFunL : E →L[ℝ] ι → ℝ) z‖ := norm_le_pi_norm _ i
      _ ≤ A * ‖z‖ := (b.equivFunL : E →L[ℝ] ι → ℝ).le_opNorm z
  have hexp : T v = ∑ w : Fin k → ι, (∏ j, b.equivFun (v j) (w j)) • T (fun j => b (w j)) := by
    conv_lhs => rw [show v = fun j => ∑ i, b.equivFun (v j) i • b i from
      funext fun j => (b.sum_equivFun (v j)).symm]
    rw [T.map_sum]
    exact Finset.sum_congr rfl (fun w _ => T.map_smul_univ _ _)
  calc ‖T v‖ ≤ ∑ w : Fin k → ι, ‖(∏ j, b.equivFun (v j) (w j)) • T (fun j => b (w j))‖ := by
        rw [hexp]; exact norm_sum_le _ _
    _ ≤ ∑ w : Fin k → ι, B * ∏ j, |b.equivFun (v j) (w j)| := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
        exact mul_le_mul_of_nonneg_right (hB w) (by positivity)
    _ = B * ∏ j, ∑ i, |b.equivFun (v j) i| := by
        rw [Finset.prod_univ_sum, Finset.mul_sum]
        rfl
    _ ≤ B * ∏ j, (Fintype.card ι * A * ‖v j‖) := by
        gcongr with j
        calc ∑ i, |b.equivFun (v j) i| ≤ ∑ _i : ι, A * ‖v j‖ :=
              Finset.sum_le_sum (fun i _ => hcoord i (v j))
          _ = Fintype.card ι * A * ‖v j‖ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ = B * (Fintype.card ι * A) ^ k * ∏ j, ‖v j‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          mul_assoc]

/-- **Coordinate form.**  Factorial bounds on the derivatives of `f` along all words in a finite
basis, locally uniformly near each point of an open set, give analyticity on that set. -/
theorem analyticOnNhd_of_basis_word_le_factorial {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    (hbound : ∀ x ∈ S, ∃ C M : ℝ, ∀ᶠ y in 𝓝 x, ∀ (k : ℕ) (w : Fin k → ι),
      ‖iteratedFDeriv ℝ k f y (fun j => b (w j))‖ ≤ C * M ^ k * k !) :
    AnalyticOnNhd ℝ f S := by
  refine analyticOnNhd_of_iteratedFDeriv_le_factorial hS hf (fun x hx => ?_)
  obtain ⟨C, M, hev⟩ := hbound x hx
  set A : ℝ := Fintype.card ι * ‖(b.equivFunL : E →L[ℝ] ι → ℝ)‖ with hA
  refine ⟨|C|, |M| * A, hev.mono fun y hy k => ?_⟩
  have hB : ∀ w : Fin k → ι, ‖iteratedFDeriv ℝ k f y (fun j => b (w j))‖ ≤ |C| * |M| ^ k * k ! := by
    intro w
    refine (hy k w).trans ?_
    have h1 : C * M ^ k ≤ |C| * |M| ^ k := by
      rw [← abs_pow, ← abs_mul]; exact le_abs_self _
    have h2 : (0 : ℝ) ≤ k ! := by positivity
    gcongr
  calc ‖iteratedFDeriv ℝ k f y‖ ≤ |C| * |M| ^ k * k ! * A ^ k :=
        norm_le_of_basis_word_le b _ (by positivity) hB
    _ = |C| * (|M| * A) ^ k * k ! := by rw [mul_pow]; ring

end Langlands.Analysis
