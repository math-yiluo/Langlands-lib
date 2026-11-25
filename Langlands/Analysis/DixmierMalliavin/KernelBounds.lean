import Langlands.Analysis.DixmierMalliavin.KernelProduct
import Mathlib.Analysis.Fourier.Convolution

/-!
# Bounds for the iterated kernels

Estimates for the objects of `KernelProduct`, for rates `a j > 0` and radii `r j > 0`:

* the remainder kernels `ρ_n` are smooth, supported in `[0, ∑_{j ≤ n} 2 r_j]`, and the derivatives
  of `ρ_{n+1}` are bounded in terms of those of `η_{n+1}` and the coefficients of
  `∏_{j ≤ n} (1 + a_j⁻¹ X)` (`norm_iteratedDeriv_stageRemainder_succ_le`);
* the Fourier transforms of the `K_n` are bounded by `1`, successive ones differ by at most
  `4π r_{n+1} |ξ| + e^{-a_{n+1} r_{n+1}}`, and `|ξ|^m ‖𝓕 K_n(ξ)‖ ≤ ∏_{j < m} a_j / π` for
  `m ≤ n + 1` (`abs_pow_mul_norm_fourier_kernelProductComplex_le`): every new factor of the
  convolution gains one power of `|ξ|`;
* the coefficients of `∏ (1 + a_j⁻¹ X)` increase with the number of factors and are bounded by any
  sequence `β` satisfying the recursive condition of `productCoeff_le_of`.

All declarations are internal to the proof of
`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add` and live in the
namespace `Langlands.Analysis.DixmierMalliavin.Line`.
-/

namespace Langlands.Analysis.DixmierMalliavin

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform



noncomputable section

namespace Line

/-- Iterated derivatives do not enlarge the topological support. -/
theorem tsupport_iteratedDeriv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (m : ℕ) : tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- If `(Φ m)' = Φ (m + 1)` for all `m`, then the `m`-th derivative of `Φ 0` is `Φ m`. -/
theorem iteratedDeriv_eq_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → ℝ → E} (h : ∀ m, deriv (Φ m) = Φ (m + 1)) (m : ℕ) : iteratedDeriv m (Φ 0) = Φ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, h]

/-- For complex functions, convolution with `ℂ`-multiplication equals convolution with the
`ℝ`-bilinear multiplication. -/
theorem convolution_mul_eq_real (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by
  funext x; simp only [convolution_def, mul_apply']

/-- Derivatives of `K ⋆ g` fall on the smooth compactly supported factor: `(K ⋆ g)^{(m)} = K ⋆ g^{(m)}`. -/
theorem iteratedDeriv_convolution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by
  have := iteratedDeriv_eq_of_deriv (Φ := fun m => K ⋆[mul ℂ ℂ] iteratedDeriv m g) (fun m => by
    funext x
    rw [convolution_mul_eq_real, convolution_mul_eq_real]
    rw [((hasCompactSupport_iteratedDeriv hgc m).hasDerivAt_convolution_right (mul ℝ ℂ) hK
      ((contDiff_iteratedDeriv_of_contDiff hg m).of_le (by simp)) x).deriv, ← iteratedDeriv_succ]) m
  simpa using this

/-- `‖(K ⋆ g)(x)‖ ≤ B ∫ ‖K‖` when `‖g‖ ≤ B`. -/
theorem norm_convolution_le {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by
  rw [convolution_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hK.norm.const_mul B)
    (Eventually.of_forall fun t => ?_))
  simp only [norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)

section Bounds

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

/-- The complex `K_n` has `L¹` norm at most `1`. -/
theorem integral_norm_kernelProductComplex_le_one (n : ℕ) :
    ∫ t, ‖kernelProductComplex a r n t‖ ≤ 1 := by
  have : (fun t => ‖kernelProductComplex a r n t‖) = kernelProduct a r n := by
    funext t; simp
        [kernelProductComplex, Complex.norm_real, abs_of_nonneg (kernelProduct_nonneg ha n t)]
  rw [this]; exact integral_kernelProduct_le_one ha hr n

/-- The remainder kernels `ρ_n` are smooth. -/
theorem contDiff_stageRemainder (n : ℕ) : ContDiff ℝ ∞ (stageRemainder a r n) := by
  cases n with
  | zero => exact contDiff_expRemainderComplex a r 0
  | succ n =>
    simp only [stageRemainder]
    exact ContDiff.sum fun p _ => contDiff_const.mul
      (contDiff_iteratedDeriv_of_contDiff (contDiff_conv_expRemainderComplex ha hr n) p)

omit ha in
/-- `ρ_n` is supported in `[0, ∑_{j ≤ n} 2 r_j]`. -/
theorem support_stageRemainder_subset (n : ℕ) : support (stageRemainder a r n) ⊆ Icc 0
    (supportBound r n) := by
  cases n with
  | zero =>
    intro t ht
    have : t ∈ Icc (r 0) (2 * r 0) := by
      by_contra h; exact ht
          (by simp [stageRemainder, expRemainderComplex, expRemainder_eq_zero (hr 0) h])
    exact ⟨(hr 0).le.trans this.1, by simpa [supportBound] using this.2⟩
  | succ n =>
    have hs : tsupport (kernelProductComplex a r n ⋆[mul ℂ ℂ] expRemainderComplex a r (n + 1)) ⊆ Icc
        0 (supportBound r (n + 1)) := by
      refine closure_minimal ?_ isClosed_Icc
      refine (support_convolution_subset (mul ℂ ℂ)).trans ?_
      have h1 : support (kernelProductComplex a r n) ⊆ Icc 0 (supportBound r n) := fun t ht =>
        support_kernelProduct_subset hr n (by simpa [kernelProductComplex] using ht)
      have h2 : support (expRemainderComplex a r (n + 1)) ⊆ Icc (r (n + 1)) (2 * r (n + 1)) :=
          fun t ht =>
        support_expRemainder_subset (hr (n + 1)) (by simpa [expRemainderComplex] using ht)
      refine (Set.add_subset_add h1 h2).trans ((Set.Icc_add_Icc_subset _ _ _ _).trans
        (Icc_subset_Icc (by linarith [hr (n + 1)]) (le_of_eq ?_)))
      simp [supportBound, Finset.sum_range_succ]
    intro t ht
    by_contra h
    apply ht
    simp only [stageRemainder]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs (tsupport_iteratedDeriv_subset p h'))),
      mul_zero]

omit ha hr in
/-- The derivatives of the complex remainder have the norms of the real ones. -/
theorem norm_iteratedDeriv_expRemainderComplex (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (expRemainderComplex a r j) t‖ =
        ‖iteratedDeriv q (expRemainder (a j) (r j)) t‖ := by
  have := iteratedDeriv_ofReal (contDiff_expRemainder (a j) (r j)) q
  show ‖iteratedDeriv q (fun t => ((expRemainder (a j) (r j) t : ℝ) : ℂ)) t‖ = _
  rw [this, Complex.norm_real]

/-- **Bound for `ρ_{n+1}`.** If `‖η_{n+1}^{(q)}‖ ≤ B q` for all `q`, then
`‖ρ_{n+1}^{(m)}‖ ≤ ∑_{p ≤ n+1} productCoeff a (n+1) p * B (p + m)`, because derivatives of
`K_n ⋆ η_{n+1}` fall on `η_{n+1}` and `K_n` has mass at most `1`. -/
theorem norm_iteratedDeriv_stageRemainder_succ_le (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (expRemainder (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (stageRemainder a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), productCoeff a (n + 1) p * B (p + m) := by
  have hKi := (integrable_kernelProductComplex ha hr n).locallyIntegrable
  have hηc := contDiff_expRemainderComplex a r (n + 1)
  have hηs := hasCompactSupport_expRemainderComplex (a := a) hr (n + 1)
  set Φ : ℕ → ℝ → ℂ := fun m u => ∑ p ∈ Finset.range (n + 2),
    (productCoeff a (n + 1) p : ℂ) *
        (kernelProductComplex a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (expRemainderComplex a r (n + 1))) u
    with hΦ
  have h0 : stageRemainder a r (n + 1) = Φ 0 := by
    funext u
    simp only [stageRemainder, hΦ, add_zero, iteratedDeriv_convolution hKi hηc hηs]
  have hd : ∀ m, deriv (Φ m) = Φ (m + 1) := by
    intro m; funext x
    have hsum := HasDerivAt.sum (u := Finset.range (n + 2))
      (A := fun p u => (productCoeff a (n + 1) p : ℂ) *
        (kernelProductComplex a r n ⋆[mul ℂ ℂ]
          iteratedDeriv (p + m) (expRemainderComplex a r (n + 1))) u)
      (A' := fun p => (productCoeff a (n + 1) p : ℂ) *
        (kernelProductComplex a r n ⋆[mul ℂ ℂ]
          iteratedDeriv (p + m + 1) (expRemainderComplex a r (n + 1))) x) (x := x)
      (fun p _ => by
        refine HasDerivAt.const_mul _ ?_
        rw [convolution_mul_eq_real, convolution_mul_eq_real, iteratedDeriv_succ]
        exact (hasCompactSupport_iteratedDeriv hηs (p + m)).hasDerivAt_convolution_right
          (mul ℝ ℂ) hKi ((contDiff_iteratedDeriv_of_contDiff hηc _).of_le (by simp)) x)
    have e : Φ m = ∑ p ∈ Finset.range (n + 2), fun u => (productCoeff a (n + 1) p : ℂ) *
        (kernelProductComplex a r n ⋆[mul ℂ ℂ]
          iteratedDeriv (p + m) (expRemainderComplex a r (n + 1))) u := by
      funext u; simp [hΦ, Finset.sum_apply]
    rw [e, hsum.deriv]
    simp only [hΦ, add_assoc]
  rw [h0, iteratedDeriv_eq_of_deriv hd m]
  simp only [hΦ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (productCoeff_nonneg ha _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (productCoeff_nonneg ha _ _)
  have hB' : ∀ u, ‖iteratedDeriv (p + m) (expRemainderComplex a r (n + 1)) u‖ ≤ B (p + m) :=
      fun u => by
    rw [norm_iteratedDeriv_expRemainderComplex]; exact hB _ _
  refine (norm_convolution_le (integrable_kernelProductComplex ha hr n) hB' t).trans ?_
  have h1 := integral_norm_kernelProductComplex_le_one ha hr n
  have h2 : 0 ≤ B (p + m) := (norm_nonneg _).trans (hB (p + m) 0)
  have h3 : 0 ≤ ∫ t, ‖kernelProductComplex a r n t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith

omit ha hr in
/-- The Fourier transform of `K_0` is that of `k_{a_0,r_0}`. -/
theorem fourier_kernelProductComplex_zero (ξ : ℝ) : 𝓕 (kernelProductComplex a r 0) ξ =
    expKernelFourier (a 0) (r 0) ξ := rfl

/-- The Fourier transform of `K_{n+1}` is the product `𝓕 K_n · 𝓕 k_{a_{n+1},r_{n+1}}`. -/
theorem fourier_kernelProductComplex_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (kernelProductComplex a r (n + 1)) ξ = 𝓕 (kernelProductComplex a r n) ξ * expKernelFourier
        (a (n + 1)) (r (n + 1)) ξ := by
  rw [kernelProductComplex_succ n, fourier_mul_convolution_eq (f₂ := expKernelComplex a r (n + 1))
    (integrable_kernelProductComplex ha hr n) (integrable_expKernel (ha (n + 1)).le (hr (n + 1))).ofReal]
  rfl

/-- The Fourier transforms of the `K_n` are bounded by `1`. -/
theorem norm_fourier_kernelProductComplex_le_one (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (kernelProductComplex a r n) ξ‖ ≤ 1 := by
  induction n with
  | zero =>
    rw [fourier_kernelProductComplex_zero]; exact norm_expKernelFourier_le_one (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_kernelProductComplex_succ ha hr, norm_mul]
    exact (mul_le_mul ih (norm_expKernelFourier_le_one (ha _) (hr _) ξ) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul 1)

/-- Successive Fourier transforms differ by at most `4π r_{n+1} |ξ| + e^{-a_{n+1} r_{n+1}}`. -/
theorem norm_fourier_kernelProductComplex_succ_sub_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (kernelProductComplex a r (n + 1)) ξ - 𝓕 (kernelProductComplex a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by
  rw [fourier_kernelProductComplex_succ ha hr, ← mul_sub_one, norm_mul]
  calc ‖𝓕 (kernelProductComplex a r n) ξ‖ * ‖expKernelFourier (a (n + 1)) (r (n + 1)) ξ - 1‖
      ≤ 1 * (4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1))) :=
        mul_le_mul (norm_fourier_kernelProductComplex_le_one ha hr n ξ)
            (norm_expKernelFourier_sub_one_le (ha _) (hr _) ξ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Decay of `𝓕 K_n`.** For `m ≤ n + 1`, `|ξ|^m ‖𝓕 K_n(ξ)‖ ≤ ∏_{j < m} a_j / π`, from the decay of
`m` of the factors and the bound `1` for the others. -/
theorem abs_pow_mul_norm_fourier_kernelProductComplex_le (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (kernelProductComplex a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by
  induction n generalizing m with
  | zero =>
    interval_cases m
    · simpa using norm_fourier_kernelProductComplex_le_one ha hr 0 ξ
    · simpa [fourier_kernelProductComplex_zero] using
        abs_mul_norm_expKernelFourier_le (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_kernelProductComplex_succ ha hr, norm_mul]
    rcases Nat.lt_or_ge m (n + 2) with h | h
    · calc |ξ| ^ m *
        (‖𝓕 (kernelProductComplex a r n) ξ‖ * ‖expKernelFourier (a (n + 1)) (r (n + 1)) ξ‖)
          ≤ |ξ| ^ m * (‖𝓕 (kernelProductComplex a r n) ξ‖ * 1) := by
            gcongr; exact norm_expKernelFourier_le_one (ha _) (hr _) ξ
        _ ≤ _ := by rw [mul_one]; exact ih m (by omega)
    · obtain rfl : m = n + 2 := le_antisymm hmn h
      rw [Finset.prod_range_succ, pow_succ]
      calc |ξ| ^ (n + 1) * |ξ| *
          (‖𝓕 (kernelProductComplex a r n) ξ‖ * ‖expKernelFourier (a (n + 1)) (r (n + 1)) ξ‖)
          = (|ξ| ^ (n + 1) * ‖𝓕 (kernelProductComplex a r n) ξ‖) *
              (|ξ| * ‖expKernelFourier (a (n + 1)) (r (n + 1)) ξ‖) := by
            ring
        _ ≤ (∏ j ∈ Finset.range (n + 1), (a j / π)) * (a (n + 1) / π) :=
            mul_le_mul (ih (n + 1) le_rfl) (abs_mul_norm_expKernelFourier_le (ha _) (hr _) ξ)
              (by positivity) (Finset.prod_nonneg fun j _ => div_nonneg (ha j).le pi_pos.le)

end Bounds

/-- The coefficients of `∏_{j < n} (1 + a_j⁻¹ X)` increase with `n`. -/
theorem productCoeff_mono {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : productCoeff a n p ≤
    productCoeff a (n + 1) p := by
  cases p with
  | zero => simp [productCoeff]
  | succ p => simp only [productCoeff]; linarith [div_nonneg (productCoeff_nonneg ha n p) (ha n).le]

/-- A bound for the coefficients of `∏_{j < n} (1 + a_j⁻¹ X)` by a sequence `β` with `β 0 = 1`: if
`a_n⁻¹ β (p - 1) ≤ 2^{-(n+1)} β p` for `1 ≤ p ≤ n + 1`, then `productCoeff a n p ≤ β p` for all
`n` (induction, with the sharper bound `β p (1 - 2^{-n})` for `p ≥ 1`). -/
theorem productCoeff_le_of {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : productCoeff a n p ≤ β p := by
  have key : ∀ n p, 1 ≤ p → productCoeff a n p ≤ β p * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [productCoeff]
    | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [productCoeff]
      have h1 := ih (q + 1) (by omega)
      have h2 : productCoeff a n q / a n ≤ (1 / 2) ^ (n + 1) * β (q + 1) := by
        rcases Nat.lt_or_ge n q with hq | hq
        · rw [productCoeff_eq_zero a hq, zero_div]
          have := hβ n (q + 1) (by omega)
          have hb : 0 ≤ β (q + 1) := hβp _
          positivity
        · have hc : productCoeff a n q ≤ β q := by
            rcases Nat.eq_zero_or_pos q with rfl | hq0
            · rw [productCoeff_zero_right, hβ0]
            · have := ih q hq0
              have hbq : 0 ≤ β q := hβp q
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
          have := hβ n (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc productCoeff a n q / a n = (a n)⁻¹ * productCoeff a n q := by ring
            _ ≤ (a n)⁻¹ * β q := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (ha n).le)
            _ ≤ _ := this
      calc productCoeff a n (q + 1) + productCoeff a n q / a n
          ≤ β (q + 1) * (1 - (1 / 2) ^ n) + (1 / 2) ^ (n + 1) * β (q + 1) := add_le_add h1 h2
        _ = β (q + 1) * (1 - (1 / 2) ^ (n + 1)) := by ring
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [productCoeff_zero_right, hβ0]
  · have := key n p hp
    nlinarith [hβp p, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

end Line

end

end Langlands.Analysis.DixmierMalliavin
