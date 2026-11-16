import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockMultiplier

/-!
# Sine-power kernels along block rotations

See the companion Markdown file.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory

namespace Langlands.Archimedean

namespace RealSwapLandingKernel

open RealBlockRotation RealBlockMultiplier RealBlockFourierFinite

/-! ## The coefficients `ĉ_r(k) = ∫₀^π sin^r θ e^{ikθ} dθ` -/

/-- The integrand `sin^r θ · e^{ikθ}`. -/
def kernelIntegrand (r : ℕ) (k : ℤ) (θ : ℝ) : ℂ :=
  ((Real.sin θ ^ r : ℝ) : ℂ) * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)

/-- `ĉ_r(k) = ∫₀^π sin^r θ e^{ikθ} dθ`. -/
def sinKernel (r : ℕ) (k : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, kernelIntegrand r k θ

theorem continuous_kernelIntegrand (r : ℕ) (k : ℤ) : Continuous (kernelIntegrand r k) := by
  unfold kernelIntegrand
  fun_prop

/-- `d/dθ (sin^{r+1} θ e^{i(k+1)θ}) = ((r+2+k)/2) sin^r θ e^{i(k+2)θ} + ((r-k)/2) sin^r θ e^{ikθ}`. -/
theorem hasDerivAt_sinPow_exp (r : ℕ) (k : ℤ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ((Real.sin θ ^ (r + 1) : ℝ) : ℂ) *
      Complex.exp (((k : ℂ) + 1) * (θ : ℂ) * Complex.I))
      (((r : ℂ) + 2 + k) / 2 * kernelIntegrand r (k + 2) θ +
        ((r : ℂ) - k) / 2 * kernelIntegrand r k θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => ((Real.sin θ ^ (r + 1) : ℝ) : ℂ))
      ((((r + 1 : ℕ) : ℝ) * Real.sin θ ^ r * Real.cos θ : ℝ) : ℂ) θ := by
    have := (Real.hasDerivAt_sin θ).pow (r + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this.ofReal_comp
  have h3 : HasDerivAt (fun θ : ℝ => ((k : ℂ) + 1) * (θ : ℂ) * Complex.I)
      (((k : ℂ) + 1) * Complex.I) θ := by
    have := ((hasDerivAt_id θ).ofReal_comp.const_mul ((k : ℂ) + 1)).mul_const Complex.I
    simpa using this
  refine (h1.mul h3.cexp).congr_deriv ?_
  set S : ℂ := ((Real.sin θ : ℝ) : ℂ) with hS
  set C : ℂ := ((Real.cos θ : ℝ) : ℂ) with hC
  set X : ℂ := Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) with hX
  have hE : Complex.exp ((θ : ℂ) * Complex.I) = C + S * Complex.I := by
    rw [Complex.exp_mul_I, hC, hS, Complex.ofReal_cos, Complex.ofReal_sin]
  have hX1 : Complex.exp (((k : ℂ) + 1) * (θ : ℂ) * Complex.I) = X * (C + S * Complex.I) := by
    rw [← hE, hX, ← Complex.exp_add]
    congr 1
    ring
  have hX2 : Complex.exp (((k + 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
      X * (C + S * Complex.I) * (C + S * Complex.I) := by
    rw [← hE, hX, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hSC : S ^ 2 + C ^ 2 = 1 := by
    rw [hS, hC]
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  unfold kernelIntegrand
  rw [hX1, hX2, ← hX]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Nat.cast_add,
    Nat.cast_one, Complex.ofReal_add, Complex.ofReal_one]
  rw [← hS, ← hC]
  linear_combination (S ^ r * X * (((r : ℂ) - k) / 2)) * hSC +
    (S ^ r * X * (((k : ℂ) + 1) * S ^ 2 - ((r : ℂ) + 2 + k) / 2 * S ^ 2)) * Complex.I_sq

/-- **Recurrence.** `ĉ_r(k+2) (r + 2 + k) = (k - r) ĉ_r(k)`. -/
theorem sinKernel_rec (r : ℕ) (k : ℤ) :
    sinKernel r (k + 2) * ((r : ℂ) + 2 + k) = ((k : ℂ) - r) * sinKernel r k := by
  have hi1 := (continuous_kernelIntegrand r (k + 2)).intervalIntegrable (μ := volume) 0 Real.pi
  have hi2 := (continuous_kernelIntegrand r k).intervalIntegrable (μ := volume) 0 Real.pi
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := Real.pi)
    (fun θ _ => hasDerivAt_sinPow_exp r k θ) ((hi1.const_mul _).add (hi2.const_mul _))
  rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simp only [Real.sin_pi, Real.sin_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, Complex.ofReal_zero, zero_mul, sub_self] at h
  unfold sinKernel
  linear_combination 2 * h

/-- `e^{-ikπ} = (-1)^k`. -/
theorem exp_neg_int_mul_pi (k : ℤ) :
    Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ k := by
  have h := Complex.exp_int_mul ((Real.pi : ℂ) * Complex.I) (-k)
  rw [Complex.exp_pi_mul_I] at h
  rw [show -((k : ℂ) * (Real.pi : ℂ) * Complex.I) = ((-k : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by
    push_cast; ring, h, zpow_neg, ← inv_zpow, inv_neg_one]

/-- **Symmetry.** `ĉ_r(-k) = (-1)^k ĉ_r(k)`. -/
theorem sinKernel_neg (r : ℕ) (k : ℤ) : sinKernel r (-k) = (-1 : ℂ) ^ k * sinKernel r k := by
  unfold sinKernel
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi)
    (kernelIntegrand r (-k)) Real.pi
  rw [sub_self, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [kernelIntegrand, Real.sin_pi_sub]
  rw [← exp_neg_int_mul_pi, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem neg_one_zpow_of_even {k : ℤ} {e : ℕ} (h : Even (k - (e : ℤ))) :
    (-1 : ℂ) ^ k = (-1 : ℂ) ^ e := by
  rw [show k = (k - e) + (e : ℤ) by ring, zpow_add₀ (by norm_num), h.neg_one_zpow, one_mul,
    zpow_natCast]

theorem isSymmetric_sinKernel (r e : ℕ) :
    IsSymmetric (e : ℤ) ((-1 : ℂ) ^ e) (sinKernel r) := fun k hk => by
  rw [sinKernel_neg, neg_one_zpow_of_even hk]

theorem isRecurrent_sinKernel (r : ℕ) (ε : ℤ) :
    IsRecurrent ((r : ℂ) + 2) ε (sinKernel r) := fun k _ => by
  have h := sinKernel_rec r k
  linear_combination h

theorem sinKernel_zero_eq (r : ℕ) :
    sinKernel r 0 = ((∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ r : ℝ) : ℂ) := by
  unfold sinKernel kernelIntegrand
  simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one]
  exact intervalIntegral.integral_ofReal

theorem sinKernel_zero_ne_zero (r : ℕ) : sinKernel r 0 ≠ 0 := by
  rw [sinKernel_zero_eq]
  exact Complex.ofReal_ne_zero.mpr (integral_sin_pow_pos (n := r)).ne'

theorem sinKernel_one_im (r : ℕ) :
    (sinKernel r 1).im = ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (r + 1) := by
  have h := intervalIntegral.intervalIntegral_im (𝕜 := ℂ)
    ((continuous_kernelIntegrand r 1).intervalIntegrable (μ := volume) 0 Real.pi)
  unfold sinKernel
  rw [← RCLike.im_to_complex, ← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [kernelIntegrand, RCLike.im_to_complex, Int.cast_one, one_mul]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re]
  ring

theorem sinKernel_one_ne_zero (r : ℕ) : sinKernel r 1 ≠ 0 := by
  intro h
  have him := sinKernel_one_im r
  rw [h, Complex.zero_im] at him
  exact (integral_sin_pow_pos (n := r + 1)).ne' him.symm

/-! ## The operators `C^r_p F(g) = ∫₀^π sin^r θ F(r_p(θ) g) dθ` -/

variable {N : ℕ}

/-- `C^r_p F(g) = ∫₀^π sin^r θ F(r_p(θ) g) dθ`. -/
def kernelOp (N p r : ℕ) (F : Langlands.GeneralLinear N ℝ → ℂ)
    (g : Langlands.GeneralLinear N ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, ((Real.sin θ ^ r : ℝ) : ℂ) * F (blockRotation N p θ * g)

theorem continuous_kernelOp (p r : ℕ) {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) : Continuous (kernelOp N p r F) := by
  unfold kernelOp
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (g : Langlands.GeneralLinear N ℝ) (θ : ℝ) =>
      ((Real.sin θ ^ r : ℝ) : ℂ) * F (blockRotation N p θ * g)) ?_ 0 Real.pi
  exact (Complex.continuous_ofReal.comp ((Real.continuous_sin.comp continuous_snd).pow r)).mul
    (hF.comp (((continuous_blockRotation N p).comp continuous_snd).mul continuous_fst))

/-- `C^r_p F` on `O(N)` only depends on `F` on `O(N)`. -/
theorem kernelOp_congr (p r : ℕ) {F₁ F₂ : Langlands.GeneralLinear N ℝ → ℂ}
    (h : ∀ x ∈ unitaryCompact ℝ N, F₁ x = F₂ x) {g : Langlands.GeneralLinear N ℝ}
    (hg : g ∈ unitaryCompact ℝ N) : kernelOp N p r F₁ g = kernelOp N p r F₂ g := by
  unfold kernelOp
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [h _ (Subgroup.mul_mem _ (blockRotation_mem_unitaryCompact N p θ) hg)]

theorem integrableOn_uIoc_prod {G : ℝ → ℝ → ℂ} (hG : Continuous (Function.uncurry G))
    (a b c d : ℝ) : IntegrableOn (Function.uncurry G) (Set.uIoc a b ×ˢ Set.uIoc c d) :=
  (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

/-- **Multiplier formula.** `Φ^p_k (C^r_p F) = ĉ_r(k) Φ^p_k F` at every point. -/
theorem blockFourierCoefficient_kernelOp {p : ℕ} (hp : p + 1 < N) (r : ℕ)
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (k : ℤ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (kernelOp N p r F) g =
      sinKernel r k * blockFourierCoefficient N p k F g := by
  unfold blockFourierCoefficient kernelOp
  simp_rw [← intervalIntegral.integral_mul_const]
  have hc : Continuous (Function.uncurry fun (θ φ : ℝ) =>
      ((Real.sin φ ^ r : ℝ) : ℂ) * F (blockRotation N p φ * (blockRotation N p θ * g)) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) := by
    refine ((Complex.continuous_ofReal.comp ((Real.continuous_sin.comp continuous_snd).pow r)).mul
      (hF.comp (((continuous_blockRotation N p).comp continuous_snd).mul
        (((continuous_blockRotation N p).comp continuous_fst).mul continuous_const)))).mul ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  rw [intervalIntegral_intervalIntegral_swap (integrableOn_uIoc_prod hc _ _ _ _)]
  unfold sinKernel kernelIntegrand
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  have e : ∀ θ : ℝ, ((Real.sin φ ^ r : ℝ) : ℂ) *
      F (blockRotation N p φ * (blockRotation N p θ * g)) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) =
      ((Real.sin φ ^ r : ℝ) : ℂ) * (F (blockRotation N p θ * (blockRotation N p φ * g)) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) := by
    intro θ
    rw [← mul_assoc (blockRotation N p φ), ← blockRotation_add, add_comm, blockRotation_add,
      mul_assoc (blockRotation N p θ)]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  have h2 := blockFourierCoefficient_blockRotation_mul hp F k φ g
  unfold blockFourierCoefficient at h2
  rw [h2]
  ring

end RealSwapLandingKernel

end Langlands.Archimedean
