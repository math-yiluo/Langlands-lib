import Langlands.Representation.Archimedean.RealSwapLandingKernel

/-!
# Rank-one intertwining integrals as sine-power kernels

See the companion Markdown file.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set

namespace Langlands.Archimedean

namespace RealSwapLandingRankOne

open RealSwapLandingKernel Langlands.GeneralLinear

/-! ## The substitution `y = cot θ` -/

/-- `cot θ = cos θ / sin θ`. -/
def cotan (θ : ℝ) : ℝ := Real.cos θ / Real.sin θ

theorem sin_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Ioo 0 Real.pi) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi h.1 h.2

theorem hasDerivAt_cotan {θ : ℝ} (h : Real.sin θ ≠ 0) :
    HasDerivAt cotan (-(Real.sin θ ^ 2)⁻¹) θ := by
  have hd := (Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) h
  have e : -Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ = -1 := by
    linear_combination -(Real.sin_sq_add_cos_sq θ)
  rw [e] at hd
  exact hd.congr_deriv (by ring)

theorem cotan_image : cotan '' Ioo 0 Real.pi = univ := by
  refine eq_univ_of_forall fun y => ⟨Real.pi / 2 - Real.arctan y, ⟨?_, ?_⟩, ?_⟩
  · linarith [Real.arctan_lt_pi_div_two y]
  · linarith [Real.neg_pi_div_two_lt_arctan y]
  · unfold cotan
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos,
      Real.tan_arctan]

theorem cotan_injOn : InjOn cotan (Ioo 0 Real.pi) := by
  intro a ha b hb hab
  have hsa := sin_pos_of_mem_Ioo ha
  have hsb := sin_pos_of_mem_Ioo hb
  unfold cotan at hab
  rw [div_eq_div_iff hsa.ne' hsb.ne'] at hab
  have h0 : Real.sin (b - a) = 0 := by
    rw [Real.sin_sub]
    linarith
  have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [ha.2, hb.1])
    (by linarith [ha.1, hb.2])).mp h0
  linarith

/-- **Substitution `y = cot θ`.** `∫_ℝ G(y) dy = ∫_{(0, π)} sin⁻² θ G(cot θ) dθ`. -/
theorem integral_eq_integral_cotan (G : ℝ → ℂ) :
    ∫ y, G y = ∫ θ in Ioo 0 Real.pi, ((Real.sin θ ^ 2)⁻¹ : ℝ) • G (cotan θ) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 Real.pi) (f := cotan)
    (f' := fun θ => -(Real.sin θ ^ 2)⁻¹) measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_cotan (sin_pos_of_mem_Ioo hθ).ne').hasDerivWithinAt) cotan_injOn G
  rw [cotan_image, Measure.restrict_univ] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]

/-! ## Rank-one integrals -/

variable {N : ℕ}

/-- **Rank-one integrals.** Let `n̄ : ℝ → GL_N(ℝ)`, `s ∈ GL_N(ℝ)` and `F` with
`F(n̄(cot θ) s x) = σ sin^{r+2} θ F(r_p(θ) x)` for `θ ∈ (0, π)` and all `x`. Then
`∫_ℝ F(n̄(y) s g) dy = σ C^r_p F (g)` for every `g`. No integrability is needed. -/
theorem integral_eq_kernelOp (p r : ℕ) (nbar : ℝ → Langlands.GeneralLinear N ℝ)
    (s : Langlands.GeneralLinear N ℝ) (σ : ℂ) {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ∀ θ ∈ Ioo 0 Real.pi, ∀ x, F (nbar (cotan θ) * s * x) =
      σ * ((Real.sin θ ^ (r + 2) : ℝ) : ℂ) * F (blockRotation N p θ * x))
    (g : Langlands.GeneralLinear N ℝ) :
    ∫ y, F (nbar y * s * g) = σ * kernelOp N p r F g := by
  rw [integral_eq_integral_cotan (fun y => F (nbar y * s * g))]
  unfold kernelOp
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  rw [hF θ hθ g]
  have hs := (sin_pos_of_mem_Ioo hθ).ne'
  have e : ((Real.sin θ ^ 2)⁻¹ : ℝ) * Real.sin θ ^ (r + 2) = Real.sin θ ^ r := by
    rw [pow_add]
    field_simp
  rw [Complex.real_smul, ← e, Complex.ofReal_mul]
  ring

/-! ## Upper triangular left translations in the principal series -/

/-- For `f` in the principal series and `B` upper triangular with diagonal `a`,
`f(B x) = (χ δ^{1/2})(a) f(x)`. -/
theorem mul_of_upperTriangular {χ : ℕ → ℝˣ → ℂ} {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) (B : Langlands.GeneralLinear N ℝ)
    (hB : (B : Matrix (Fin N) (Fin N) ℝ).BlockTriangular id) (a : Fin N → ℝˣ)
    (ha : ∀ i, (a i : ℝ) = (B : Matrix (Fin N) (Fin N) ℝ) i i)
    (x : Langlands.GeneralLinear N ℝ) :
    f (B * x) = principalSeriesCharacter ℝ N χ a * f x := by
  set D : Langlands.GeneralLinear N ℝ := Iwasawa.diagonalUnits a with hD
  have hDinv : ((D⁻¹ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.diagonal fun i => (((a i)⁻¹ : ℝˣ) : ℝ) := rfl
  have hval : ((D⁻¹ * B : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.diagonal (fun i => (((a i)⁻¹ : ℝˣ) : ℝ)) * (B : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Units.val_mul, hDinv]
  have hu : D⁻¹ * B ∈ upperUnipotent N ℝ := by
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * B : Langlands.GeneralLinear N ℝ) :
        Matrix (Fin N) (Fin N) ℝ).BlockTriangular id
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hB
    · change ((D⁻¹ * B : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i i = 1
      rw [hval, Matrix.diagonal_mul, ← ha i]
      exact Units.inv_mul (a i)
  have hBx : B * x = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear N ℝ) *
      ((⟨D⁻¹ * B, hu⟩ : upperUnipotent N ℝ) : Langlands.GeneralLinear N ℝ) * x := by
    rw [← hD]
    simp
  rw [hBx, hf.2 a ⟨D⁻¹ * B, hu⟩ x]

end RealSwapLandingRankOne

end Langlands.Archimedean
