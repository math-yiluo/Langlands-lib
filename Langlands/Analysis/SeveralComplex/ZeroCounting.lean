import Langlands.Analysis.SeveralComplex.ArgumentPrinciple
import Langlands.Analysis.SeveralComplex.LineDerivative
import Langlands.Analysis.SeveralComplex.PowerSumInterpolation

/-! # Power sums over the zeros of a holomorphic family in one variable

Let `P` be a finite-dimensional complex normed space and let `H : P × ℂ → ℂ` be holomorphic on
an open set `O ⊆ P × ℂ` which contains `{0} × closedBall 0 ρ`, with `H (0, t) ≠ 0` on the circle
`|t| = ρ`. For a family `b : Λ → P × ℂ → F` of maps holomorphic on `O` we construct, near
`w = 0`, holomorphic maps `T l : P → (Fin k → F)` whose coordinates are the weighted power sums
`∑ ord_u H(w, ·) · u^j · b l (w, u)` over the zeros `u` of `H (w, ·)` in the disc `|t| < ρ`
(by the argument principle these are circle integrals, hence holomorphic in `w`), where `k` is
the number of these zeros counted with multiplicity (locally constant in `w`).

The main result `exists_powerSum_family` says: whenever the span of the `T l w` is spanned by
the `T μ w` with `μ ∈ s₀`, then at every zero `t` of `H (w, ·)` in the disc the span of the
`b l (w, t)` is spanned by the `b μ (w, t)` with `μ ∈ s₀`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Complex MeromorphicOn
open scoped Topology Real

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The derivative in `t` of `H (w, t)` is the directional derivative of `H` along `(0, 1)`. -/
theorem hasDerivAt_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {H : P × ℂ → G} {w : P} {t : ℂ} (hd : DifferentiableAt ℂ H (w, t)) :
    HasDerivAt (fun s : ℂ => H (w, s)) (fderiv ℂ H (w, t) ((0 : P), (1 : ℂ))) t := by
  have h1 : HasDerivAt (fun s : ℂ => ((w : P), s)) ((0 : P), (1 : ℂ)) t :=
    (hasDerivAt_const t w).prodMk (hasDerivAt_id t)
  exact hd.hasFDerivAt.comp_hasDerivAt t h1

variable [FiniteDimensional ℂ P]

/-- Integrals over the circle `|t| = ρ` of `(K / H) • Ψ` are holomorphic in the parameter `w` on
an open set `W` over which `H` has no zero on the circle. -/
theorem differentiableOn_circleIntegral_div_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {O : Set (P × ℂ)} {H K : P × ℂ → ℂ} (hH : DifferentiableOn ℂ H O)
    (hK : DifferentiableOn ℂ K O) {Ψ : P × ℂ → G} (hΨ : DifferentiableOn ℂ Ψ O) {W : Set P}
    (hW : IsOpen W) {ρ : ℝ} (hρ : 0 < ρ)
    (hWO : ∀ w ∈ W, ∀ t ∈ sphere (0 : ℂ) ρ, (w, t) ∈ O ∧ H (w, t) ≠ 0) :
    DifferentiableOn ℂ (fun w => ∮ t in C(0, ρ), (K (w, t) / H (w, t)) • Ψ (w, t)) W := by
  set O' := {p ∈ O | H p ≠ 0} with hO'
  have hd : DifferentiableOn ℂ (fun p => (K p / H p) • Ψ p) O' := by
    have h1 : DifferentiableOn ℂ (fun p => K p * (H p)⁻¹) O' :=
      (hK.mono (sep_subset _ _)).fun_mul
        ((hH.mono (sep_subset _ _)).fun_inv fun p (hp : p ∈ O') => hp.2)
    simp_rw [div_eq_mul_inv]
    exact h1.smul (hΨ.mono (sep_subset _ _))
  refine differentiableOn_circleIntegral_of_continuousOn hW ?_ ?_
  · refine hd.continuousOn.mono ?_
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    rw [abs_of_pos hρ] at ht
    exact hWO w hw t ht
  · intro t ht
    rw [abs_of_pos hρ] at ht
    refine hd.comp (differentiableOn_id.prodMk (differentiableOn_const t)) ?_
    intro w hw
    exact hWO w hw t ht

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℂ P] in
/-- The argument principle for the slice `t ↦ H (w, t)`, with the `t`-derivative written as the
directional derivative of `H` along `(0, 1)`. -/
theorem circleIntegral_slice_eq {O : Set (P × ℂ)} (hO : IsOpen O) {H : P × ℂ → ℂ}
    (hH : DifferentiableOn ℂ H O) {Ψ : P × ℂ → F} (hΨ : DifferentiableOn ℂ Ψ O) {w : P}
    {v : Set ℂ} (hv : IsOpen v) (hvO : ∀ t ∈ v, (w, t) ∈ O) {ρ : ℝ} (hρ : 0 < ρ)
    (hBv : closedBall (0 : ℂ) ρ ⊆ v) (hne : ∀ t ∈ sphere (0 : ℂ) ρ, H (w, t) ≠ 0) :
    (∮ t in C(0, ρ), (fderiv ℂ H (w, t) ((0 : P), (1 : ℂ)) / H (w, t)) • Ψ (w, t)) =
      (2 * π * I : ℂ) • ∑ᶠ u, ((divisor (fun s => H (w, s)) (closedBall 0 ρ) u : ℤ) : ℂ) •
        Ψ (w, u) := by
  have hpair : DifferentiableOn ℂ (fun s : ℂ => ((w : P), s)) v :=
    (differentiableOn_const w).prodMk differentiableOn_id
  have hsH : DifferentiableOn ℂ (fun s => H (w, s)) v := hH.comp hpair fun t ht => hvO t ht
  have hsΨ : DifferentiableOn ℂ (fun s => Ψ (w, s)) v := hΨ.comp hpair fun t ht => hvO t ht
  have hderiv : ∀ t ∈ sphere (0 : ℂ) ρ,
      fderiv ℂ H (w, t) ((0 : P), (1 : ℂ)) = deriv (fun s => H (w, s)) t := by
    intro t ht
    have htO : (w, t) ∈ O := hvO t (hBv (sphere_subset_closedBall ht))
    exact (hasDerivAt_slice ((hH _ htO).differentiableAt (hO.mem_nhds htO))).deriv.symm
  rw [circleIntegral.integral_congr hρ.le fun t ht => by rw [hderiv t ht]]
  exact circleIntegral_logDeriv_smul hρ hv hBv hsH hne hsΨ

/-- **Power sums over zeros, holomorphic in the parameter.** See the module docstring. -/
theorem exists_powerSum_family {Λ : Type*} {O : Set (P × ℂ)} (hO : IsOpen O) {H : P × ℂ → ℂ}
    (hH : DifferentiableOn ℂ H O) {b : Λ → P × ℂ → F} (hb : ∀ l, DifferentiableOn ℂ (b l) O)
    {ρ : ℝ} (hρ : 0 < ρ) (hρO : ∀ t ∈ closedBall (0 : ℂ) ρ, ((0 : P), t) ∈ O)
    (hne : ∀ t ∈ sphere (0 : ℂ) ρ, H (0, t) ≠ 0) :
    ∃ k : ℕ, ∃ δ > 0, ∃ T : Λ → P → (Fin k → F),
      (∀ l, DifferentiableOn ℂ (T l) (ball 0 δ)) ∧
      ∀ w ∈ ball (0 : P) δ, ∀ s₀ : Set Λ,
        (∀ l, T l w ∈ Submodule.span ℂ ((fun μ => T μ w) '' s₀)) →
        ∀ t ∈ ball (0 : ℂ) ρ, H (w, t) = 0 →
          ∀ l, b l (w, t) ∈ Submodule.span ℂ ((fun μ => b μ (w, t)) '' s₀) := by
  classical
  -- tubes around `{0} × closedBall 0 ρ` and `{0} × sphere 0 ρ`
  obtain ⟨u, v, hu, hv, h0u, hBv, huvO⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : P))) (isCompact_closedBall (0 : ℂ) ρ) hO (by
      rintro ⟨w, t⟩ ⟨hw, ht⟩
      have hw' : w = 0 := hw
      subst hw'
      exact hρO t ht)
  set O₁ := O ∩ H ⁻¹' {0}ᶜ with hO₁def
  have hO₁ : IsOpen O₁ := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  obtain ⟨u₁, v₁, hu₁, -, h0u₁, hSv₁, huvO₁⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : P))) (isCompact_sphere (0 : ℂ) ρ) hO₁ (by
      rintro ⟨w, t⟩ ⟨hw, ht⟩
      have hw' : w = 0 := hw
      subst hw'
      exact ⟨hρO t (sphere_subset_closedBall ht), hne t ht⟩)
  obtain ⟨δ₀, hδ₀, hδ₀u⟩ := Metric.isOpen_iff.1 (hu.inter hu₁) 0
    ⟨h0u (mem_singleton _), h0u₁ (mem_singleton _)⟩
  have hwv : ∀ w ∈ ball (0 : P) δ₀, ∀ t ∈ v, (w, t) ∈ O := fun w hw t ht =>
    huvO ⟨(hδ₀u hw).1, ht⟩
  have hwS : ∀ w ∈ ball (0 : P) δ₀, ∀ t ∈ sphere (0 : ℂ) ρ, (w, t) ∈ O ∧ H (w, t) ≠ 0 :=
    fun w hw t ht => huvO₁ ⟨(hδ₀u hw).2, hSv₁ ht⟩
  -- the `t`-derivative of `H`
  set K : P × ℂ → ℂ := fun p => fderiv ℂ H p ((0 : P), (1 : ℂ)) with hKdef
  have hK : DifferentiableOn ℂ K O := differentiableOn_fderiv_apply hO hH _
  -- divisors of the slices
  set D : P → Function.locallyFinsuppWithin (closedBall (0 : ℂ) ρ) ℤ :=
    fun w => divisor (fun s => H (w, s)) (closedBall 0 ρ) with hDdef
  have hslice : ∀ w ∈ ball (0 : P) δ₀, DifferentiableOn ℂ (fun s => H (w, s)) v := by
    intro w hw
    exact hH.comp ((differentiableOn_const w).prodMk differentiableOn_id) fun t ht => hwv w hw t ht
  have hD0 : ∀ w ∈ ball (0 : P) δ₀, 0 ≤ D w := by
    intro w hw
    exact (((hslice w hw).analyticOnNhd hv).mono hBv).divisor_nonneg
  have hDfin : ∀ w, (D w).support.Finite := fun w => divisor_closedBall_support_finite
  -- the number of zeros, counted with multiplicity
  set N : P → ℤ := fun w => ∑ᶠ u, D w u with hNdef
  have hNint : ∀ w ∈ ball (0 : P) δ₀,
      (∮ t in C(0, ρ), (K (w, t) / H (w, t)) • (fun _ : P × ℂ => (1 : ℂ)) (w, t)) =
        (2 * π * I : ℂ) • ((N w : ℤ) : ℂ) := by
    intro w hw
    rw [circleIntegral_slice_eq hO hH (differentiableOn_const (1 : ℂ)) hv (hwv w hw) hρ hBv
      fun t ht => (hwS w hw t ht).2]
    congr 1
    simp only [smul_eq_mul, mul_one, hNdef]
    exact ((Int.castAddHom ℂ).map_finsum (hDfin w)).symm
  have hNcont : ContinuousAt (fun w => ((N w : ℤ) : ℂ)) 0 := by
    have hd := differentiableOn_circleIntegral_div_smul hH hK (Ψ := fun _ : P × ℂ => (1 : ℂ))
      (differentiableOn_const 1) isOpen_ball hρ hwS
    have hc : ContinuousAt (fun w =>
        ∮ t in C(0, ρ), (K (w, t) / H (w, t)) • (fun _ : P × ℂ => (1 : ℂ)) (w, t)) 0 :=
      (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ₀))).continuousAt
    refine (hc.const_smul (2 * π * I : ℂ)⁻¹).congr ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ₀)] with w hw
    show (2 * π * I : ℂ)⁻¹ •
      (∮ t in C(0, ρ), (K (w, t) / H (w, t)) • (fun _ : P × ℂ => (1 : ℂ)) (w, t)) = _
    rw [hNint w hw, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  have hNev : ∀ᶠ w in 𝓝 (0 : P), N w = N 0 := by
    filter_upwards [hNcont (ball_mem_nhds _ one_pos)] with w hw
    rw [Set.mem_preimage, mem_ball, dist_eq_norm, ← Int.cast_sub, norm_intCast] at hw
    by_contra hne'
    have := Int.one_le_abs (sub_ne_zero.2 hne')
    have h' : (1 : ℝ) ≤ |((N w - N 0 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast this
    linarith
  obtain ⟨δ₁, hδ₁, hδ₁N⟩ := Metric.mem_nhds_iff.1 hNev
  set δ := min δ₀ δ₁ with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hδ₀' : ball (0 : P) δ ⊆ ball 0 δ₀ := ball_subset_ball (min_le_left _ _)
  have hN0 : 0 ≤ N 0 := finsum_nonneg fun u => hD0 0 (mem_ball_self hδ₀) u
  set k : ℕ := (N 0).toNat with hkdef
  have hNk : ∀ w ∈ ball (0 : P) δ, N w = k := by
    intro w hw
    rw [hδ₁N (ball_subset_ball (min_le_right _ _) hw), hkdef, Int.toNat_of_nonneg hN0]
  -- the power-sum family
  set T : Λ → P → (Fin k → F) := fun l w j => (2 * π * I : ℂ)⁻¹ •
    ∮ t in C(0, ρ), (K (w, t) / H (w, t)) • (fun p : P × ℂ => p.2 ^ (j : ℕ) • b l p) (w, t)
    with hTdef
  refine ⟨k, δ, hδ, T, ?_, ?_⟩
  · intro l
    refine differentiableOn_pi.2 fun j => ?_
    refine (DifferentiableOn.const_smul ?_ _).mono hδ₀'
    refine differentiableOn_circleIntegral_div_smul
      (Ψ := fun p : P × ℂ => p.2 ^ (j : ℕ) • b l p) hH hK ?_ isOpen_ball hρ hwS
    exact (differentiableOn_snd.pow _).smul (hb l)
  · intro w hw s₀ hT t ht hHt l
    have hw₀ : w ∈ ball (0 : P) δ₀ := hδ₀' hw
    set S : Finset ℂ := (hDfin w).toFinset with hSdef
    -- `T μ w` is the power-sum vector of `b μ (w, ·)` over the zeros
    have hTeq : ∀ μ, T μ w =
        powerSumVector k S (fun u => ((D w u : ℤ) : ℂ)) (fun u => b μ (w, u)) := by
      intro μ
      funext j
      simp only [hTdef, powerSumVector]
      rw [circleIntegral_slice_eq hO hH (Ψ := fun p : P × ℂ => p.2 ^ (j : ℕ) • b μ p)
        ((differentiableOn_snd.pow _).smul (hb μ)) hv (hwv w hw₀) hρ hBv
        fun t ht => (hwS w hw₀ t ht).2, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
      rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
      intro u hu
      rw [hSdef, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      apply hu
      have h0' : divisor (fun s => H (w, s)) (closedBall 0 ρ) u = 0 := h0
      simp [h0']
    -- the zero `t` is a point of `S`
    have hDt : D w t ≠ 0 :=
      (divisor_closedBall_ne_zero_iff hρ hv hBv (hslice w hw₀)
        fun s hs => (hwS w hw₀ s hs).2).2 ⟨ht, hHt⟩
    have htS : t ∈ S := by
      rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
      exact hDt
    -- at most `k` distinct zeros
    have hcard : S.card ≤ k := by
      have hsum : N w = ∑ u ∈ S, D w u := by
        simp only [hNdef]
        rw [finsum_eq_sum_of_support_subset _ (s := S) (by
          rw [hSdef, Set.Finite.coe_toFinset])]
      have hle : ((S.card : ℕ) : ℤ) ≤ ∑ u ∈ S, D w u := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        refine Finset.sum_le_sum fun u hu => ?_
        have h1 : D w u ≠ 0 := by
          rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support] at hu
          exact hu
        have h2 : 0 ≤ D w u := hD0 w hw₀ u
        omega
      rw [← hsum, hNk w hw] at hle
      exact_mod_cast hle
    have hT' : ∀ l, powerSumVector k S (fun u => ((D w u : ℤ) : ℂ)) (fun u => b l (w, u)) ∈
        Submodule.span ℂ ((fun μ => powerSumVector k S (fun u => ((D w u : ℤ) : ℂ))
          (fun u => b μ (w, u))) '' s₀) := by
      intro l
      have := hT l
      simp only [hTeq] at this
      exact this
    exact mem_span_of_powerSumVector_mem_span (c := fun μ u => b μ (w, u)) hcard hT' htS
      (by exact_mod_cast hDt) l

end Langlands.Analysis.SeveralComplex
