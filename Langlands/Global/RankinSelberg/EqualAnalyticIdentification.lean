import Langlands.Global.RankinSelberg.EqualAnalyticContinuation

/-! # Splitting the theta kernel with Poisson summation

For `Re s` large, with `c(t) = ∫_(L<0) P e^(t L)` and `d(t) = ∫_(L≥0) P e^(t L)`:

* `∫ K_s = A(s) + Ã(1 - s) + Φ̂(0) c(s - 1) - Φ(0) c(s)` (`integral_kernel_eq`), from
  `Θ(g) = e^(-L(g)) (Θ(Φ̂, ᵗg⁻¹) + Φ̂(0)) - Φ(0)` on `L < 0`;
* `∫ K̃_s = Ã(s) + A(1 - s) + Φ(0) d(1 - s) - Φ̂(0) d(-s)` for the dual kernel
  `K̃_s(g) = P(ᵗg⁻¹) |det g|^s Θ(Φ̂, g)` (`integral_dual_kernel_eq`), after the substitution
  `g ↦ ᵗg⁻¹` and Poisson summation on `L ≥ 0`;
* both kernels have finite majorant integrals for `Re s` large
  (`lintegral_kernel_lt_top`, `lintegral_dual_kernel_lt_top`).
-/

noncomputable section
set_option linter.unusedSectionVars false
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance identSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance identSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local notation "E" => GeneralLinearGroupPoints.adelicEquiv

namespace EqualData

variable {F : Type u} [Field F] [NumberField F] {r : ℕ} (D : EqualData F r)
  [CompactSpace (AdeleQuotient F)]

/-- The dual product `g ↦ P(ᵗg⁻¹)`. -/
def Pd (g : Points F (r + 1)) : ℂ := D.P (iota F (r + 1) g)

theorem poisson (g : Points F (r + 1)) :
    D.Θ g + D.Φ 0 = Complex.exp (-(Lg g : ℂ)) * (D.Θι g + D.Φh 0) :=
  thetaSum_poisson_points (r + 1) D.ψ D.hψ D.hΦ g

theorem kernel_decomp (s : ℂ) (g : Points F (r + 1)) :
    thetaKernel F r D.P D.Φ s g = D.amp₁ g * Complex.exp (s * (Lg g : ℝ)) +
      D.amp₂ g * Complex.exp ((1 - s) * (-Lg g : ℝ)) + D.Φh 0 * resLt F r D.P (s - 1) g -
        D.Φ 0 * resLt F r D.P s g := by
  have hΘ : D.Θ g = Complex.exp (-(Lg g : ℂ)) * (D.Θι g + D.Φh 0) - D.Φ 0 :=
    eq_sub_of_add_eq (D.poisson g)
  have hk : thetaKernel F r D.P D.Φ s g =
      D.P g * Complex.exp (s * (Lg g : ℝ)) * D.Θ g := rfl
  rw [hk]
  by_cases h : 0 ≤ Lg g
  · have h' : ¬ Lg g < 0 := not_lt.2 h
    have h'' : ¬ Real.log (detNorm F (r + 1) g) < 0 := h'
    simp only [amp₁, amp₂, resLt, h, h', h'', ↓reduceIte]
    ring
  · have h' : Lg g < 0 := lt_of_not_ge h
    have h'' : Real.log (detNorm F (r + 1) g) < 0 := h'
    simp only [amp₁, amp₂, resLt, h, h', h'', ↓reduceIte]
    rw [hΘ]
    have e1 : (1 - s) * (((-Lg g : ℝ)) : ℂ) = s * (Lg g : ℂ) + -(Lg g : ℂ) := by push_cast; ring
    have e2 : (s - 1) * ((Real.log (detNorm F (r + 1) g) : ℝ) : ℂ) =
        s * (Lg g : ℂ) + -(Lg g : ℂ) := by rw [Lg]; ring
    have e3 : s * ((Real.log (detNorm F (r + 1) g) : ℝ) : ℂ) = s * (Lg g : ℂ) := rfl
    rw [e1, e2, e3, Complex.exp_add]
    ring

theorem dual_kernel_decomp (s : ℂ) (g : Points F (r + 1)) :
    thetaKernel F r D.Pd D.Φh s (iota F (r + 1) g) =
      D.amp₂ g * Complex.exp (s * (-Lg g : ℝ)) + D.amp₁ g * Complex.exp ((1 - s) * (Lg g : ℝ)) +
        D.Φ 0 * resGe F r D.P (1 - s) g - D.Φh 0 * resGe F r D.P (-s) g := by
  have hΘι : D.Θι g = Complex.exp (Lg g : ℂ) * (D.Θ g + D.Φ 0) - D.Φh 0 := by
    rw [D.poisson g, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul,
      add_sub_cancel_right]
  have hk : thetaKernel F r D.Pd D.Φh s (iota F (r + 1) g) =
      D.P g * Complex.exp (s * (-Lg g : ℝ)) * D.Θι g := by
    simp only [thetaKernel, Pd, UnequalAnalytic.iota_iota, detPower, log_detNorm_iota, Θι, Lg]
  rw [hk]
  by_cases h : 0 ≤ Lg g
  · have h' : ¬ Lg g < 0 := not_lt.2 h
    have h'' : 0 ≤ Real.log (detNorm F (r + 1) g) := h
    simp only [amp₁, amp₂, resGe, h, h', h'', ↓reduceIte]
    rw [hΘι]
    have e1 : s * (((-Lg g : ℝ)) : ℂ) + (Lg g : ℂ) = (1 - s) * (Lg g : ℂ) := by push_cast; ring
    have e2 : (1 - s) * ((Real.log (detNorm F (r + 1) g) : ℝ) : ℂ) = (1 - s) * (Lg g : ℂ) := rfl
    have e3 : -s * ((Real.log (detNorm F (r + 1) g) : ℝ) : ℂ) = s * (((-Lg g : ℝ)) : ℂ) := by
      rw [Lg]; push_cast; ring
    rw [e2, e3, ← e1, Complex.exp_add]
    ring
  · have h' : Lg g < 0 := lt_of_not_ge h
    have h'' : ¬ 0 ≤ Real.log (detNorm F (r + 1) g) := h
    simp only [amp₁, amp₂, resGe, h, h', h'', ↓reduceIte]
    ring

theorem Pd_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.Pd (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.Pd g :=
  iota_rational_mul_invariant D.hPr c g

theorem continuous_Pd : Continuous D.Pd :=
  D.hPc.comp (UnequalAnalytic.continuous_iota F (r + 1))

/-- **The kernel split for `Re s` large.** -/
theorem integral_kernel_eq (s : ℂ)
    (h1 : Integrable (fun x => resLt F r D.P (s - 1) (Quotient.out x)) μq)
    (h2 : Integrable (fun x => resLt F r D.P s (Quotient.out x)) μq) :
    ∫ x, thetaKernel F r D.P D.Φ s (Quotient.out x) ∂μq =
      D.A s + D.At (1 - s) + D.Φh 0 * ∫ x, resLt F r D.P (s - 1) (Quotient.out x) ∂μq -
        D.Φ 0 * ∫ x, resLt F r D.P s (Quotient.out x) ∂μq := by
  have i1 := D.integrable_A_integrand s
  have i2 := D.integrable_At_integrand (1 - s)
  have i3 := h1.const_mul (D.Φh 0)
  have i4 := h2.const_mul (D.Φ 0)
  simp only [D.kernel_decomp s]
  have e1 := integral_sub ((i1.add i2).add i3) i4
  have e2 := integral_add (i1.add i2) i3
  have e3 := integral_add i1 i2
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3, integral_const_mul, integral_const_mul]
  rfl

/-- **The dual kernel split for `Re s` large.** -/
theorem integral_dual_kernel_eq (s : ℂ)
    (h1 : Integrable (fun x => resGe F r D.P (1 - s) (Quotient.out x)) μq)
    (h2 : Integrable (fun x => resGe F r D.P (-s) (Quotient.out x)) μq) :
    ∫ x, thetaKernel F r D.Pd D.Φh s (Quotient.out x) ∂μq =
      D.At s + D.A (1 - s) + D.Φ 0 * ∫ x, resGe F r D.P (1 - s) (Quotient.out x) ∂μq -
        D.Φh 0 * ∫ x, resGe F r D.P (-s) (Quotient.out x) ∂μq := by
  rw [integral_out_iota (thetaKernel_rational_mul F r D.Pd_rational_mul D.Φh s)]
  have i1 := D.integrable_At_integrand s
  have i2 := D.integrable_A_integrand (1 - s)
  have i3 := h1.const_mul (D.Φ 0)
  have i4 := h2.const_mul (D.Φh 0)
  simp only [D.dual_kernel_decomp s]
  have e1 := integral_sub ((i1.add i2).add i3) i4
  have e2 := integral_add (i1.add i2) i3
  have e3 := integral_add i1 i2
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3, integral_const_mul, integral_const_mul]
  rfl

theorem enorm_detPower_eq {n : ℕ} (g : Points F n) (s : ℂ) :
    ‖detPower F n g s‖ₑ = ENNReal.ofReal (Real.exp (s.re * Real.log (detNorm F n g))) := by
  rw [detPower, ← ofReal_norm, Complex.norm_exp, Complex.re_mul_ofReal]

theorem thetaKernelNorm_split (s : ℂ) (g : Points F (r + 1)) :
    thetaKernelNorm F r D.P D.Φ s g = regionGe D.P s.re D.V₁ g + regionLt D.P s.re D.V₁ g := by
  rw [thetaKernelNorm, enorm_detPower_eq]
  by_cases h : 0 ≤ Real.log (detNorm F (r + 1) g)
  · rw [regionGe, regionLt, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h), Set.indicator_of_notMem
      (show g ∉ {g : Points F (r + 1) | Real.log (detNorm F (r + 1) g) < 0} from not_lt.2 h),
      add_zero]
    rfl
  · rw [regionGe, regionLt, Set.indicator_of_notMem (show g ∉ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h), Set.indicator_of_mem
      (show g ∈ {g : Points F (r + 1) | Real.log (detNorm F (r + 1) g) < 0} from lt_of_not_ge h),
      zero_add]
    rfl

theorem dual_thetaKernelNorm_split (s : ℂ) (g : Points F (r + 1)) :
    thetaKernelNorm F r D.Pd D.Φh s (iota F (r + 1) g) =
      regionGe D.P (-s.re) D.V₂ g + regionLt D.P (-s.re) D.V₂ g := by
  have hk : thetaKernelNorm F r D.Pd D.Φh s (iota F (r + 1) g) = ‖D.P g‖ₑ *
      ENNReal.ofReal (Real.exp (-s.re * Real.log (detNorm F (r + 1) g))) * D.V₂ g := by
    rw [thetaKernelNorm, enorm_detPower_eq, log_detNorm_iota, Pd, UnequalAnalytic.iota_iota,
      show s.re * -Real.log (detNorm F (r + 1) g) = -s.re * Real.log (detNorm F (r + 1) g) by
        ring]
    rfl
  rw [hk]
  by_cases h : 0 ≤ Real.log (detNorm F (r + 1) g)
  · rw [regionGe, regionLt, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h), Set.indicator_of_notMem
      (show g ∉ {g : Points F (r + 1) | Real.log (detNorm F (r + 1) g) < 0} from not_lt.2 h),
      add_zero]
  · rw [regionGe, regionLt, Set.indicator_of_notMem (show g ∉ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h), Set.indicator_of_mem
      (show g ∈ {g : Points F (r + 1) | Real.log (detNorm F (r + 1) g) < 0} from lt_of_not_ge h),
      zero_add]

/-- **Finiteness of the kernel majorant.** -/
theorem lintegral_kernel_lt_top {s : ℂ}
    (hs : 1 ≤ s.re * Module.finrank ℚ F - (((r + 1) * Module.finrank ℚ F + 1 : ℕ) : ℝ) /
      ((r + 1 : ℕ) : ℝ) - D.A₀) :
    ∫⁻ x, thetaKernelNorm F r D.P D.Φ s (Quotient.out x) ∂μq < ⊤ := by
  simp only [D.thetaKernelNorm_split s]
  rw [lintegral_add_left (measurable_out (measurable_regionGe D.hPc _ D.measurable_V₁)
    (regionGe_rational_mul D.hPr _ D.V₁_rational_mul))]
  exact ENNReal.add_lt_top.2 ⟨D.lintegral_ge_V₁_lt_top _, D.lintegral_lt_V₁_lt_top hs⟩

/-- **Finiteness of the dual kernel majorant.** -/
theorem lintegral_dual_kernel_lt_top {s : ℂ}
    (hs : -s.re * Module.finrank ℚ F + (((r + 1) * Module.finrank ℚ F + 1 : ℕ) : ℝ) /
      ((r + 1 : ℕ) : ℝ) + D.A₀ ≤ -1) :
    ∫⁻ x, thetaKernelNorm F r D.Pd D.Φh s (Quotient.out x) ∂μq < ⊤ := by
  rw [lintegral_out_iota (thetaKernelNorm_rational_mul F r D.Pd_rational_mul D.Φh s)]
  simp only [D.dual_thetaKernelNorm_split s]
  rw [lintegral_add_left (measurable_out (measurable_regionGe D.hPc _ D.measurable_V₂)
    (regionGe_rational_mul D.hPr _ D.V₂_rational_mul))]
  exact ENNReal.add_lt_top.2 ⟨D.lintegral_ge_V₂_lt_top hs, D.lintegral_lt_V₂_lt_top _⟩

end EqualData

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
