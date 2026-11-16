import Langlands.Global.RankinSelberg.EqualAnalyticIdentification
import Langlands.Global.RankinSelberg.EqualAnalyticPoles

/-! # The analytic continuation and functional equation for `EqualData`

With `A`, `Ã` entire and `C_w = ∫_(D ∩ S) P |det|^(-w/n)`:

* if `χ = |·|^w`, set
  `I(s) = A(s) + Ã(1 - s) + Φ̂(0) C_w / (n(s - 1) + w) - Φ(0) C_w / (n s + w)` and
  `Ĩ(s) = Ã(s) + A(1 - s) - Φ(0) C_w / (n(1 - s) + w) + Φ̂(0) C_w / (-n s + w)`;
* otherwise `I(s) = A(s) + Ã(1 - s)` and `Ĩ(s) = Ã(s) + A(1 - s)`.

Then for `Re s` large both kernels are absolutely integrable over `GL_n(F) \ GL_n(𝔸)` with
integrals `I(s)` and `Ĩ(s)`; `I` and `Ĩ` have at most simple poles in `P(χ)` and `P(χ⁻¹)`, `I` is
bounded in vertical strips away from `P(χ)`, and `I(s) = Ĩ(1 - s)` (`EqualData.main`).
-/

noncomputable section
set_option linter.unusedSectionVars false
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance mainSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance mainSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

namespace EqualData

variable {F : Type u} [Field F] [NumberField F] {r : ℕ} (D : EqualData F r)
  [CompactSpace (AdeleQuotient F)]

/-- The constant `(N₀ : ℝ) / n` with `N₀ = n [F:ℚ] + 1`. -/
abbrev Nn : ℝ := (((r + 1) * Module.finrank ℚ F + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)

/-- The abscissa beyond which everything converges. -/
def σ₀ (w : ℂ) : ℝ :=
  1 + (1 + Nn (F := F) (r := r) + |D.A₀|) / Module.finrank ℚ F + |w.re| / ((r + 1 : ℕ) : ℝ)

theorem conditions (w s : ℂ) (hs : D.σ₀ w < s.re) :
    1 ≤ s.re * Module.finrank ℚ F - Nn (F := F) (r := r) - D.A₀ ∧
    -s.re * Module.finrank ℚ F + Nn (F := F) (r := r) + D.A₀ ≤ -1 ∧
    1 ≤ (s - 1).re * Module.finrank ℚ F + 0 - D.A₀ ∧
    1 ≤ s.re * Module.finrank ℚ F + 0 - D.A₀ ∧
    (1 - s).re * Module.finrank ℚ F + 0 + D.A₀ ≤ -1 ∧
    (-s).re * Module.finrank ℚ F + 0 + D.A₀ ≤ -1 ∧
    0 < (w + ((r + 1 : ℕ) : ℂ) * (s - 1)).re ∧ 0 < (w + ((r + 1 : ℕ) : ℂ) * s).re ∧
    (w + ((r + 1 : ℕ) : ℂ) * (1 - s)).re < 0 ∧ (w + ((r + 1 : ℕ) : ℂ) * (-s)).re < 0 := by
  have hA₀ : 0 ≤ D.A₀ := D.hPd.1
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos r)
  have hNn : 0 ≤ Nn (F := F) (r := r) := by positivity
  set d : ℝ := (Module.finrank ℚ F : ℝ)
  set N := Nn (F := F) (r := r)
  set m : ℝ := ((r + 1 : ℕ) : ℝ)
  set T := (1 + N + |D.A₀|) / d with hT
  set W := |w.re| / m with hW
  have hTd : T * d = 1 + N + D.A₀ := by rw [hT, abs_of_nonneg hA₀]; field_simp
  have hWm : W * m = |w.re| := by rw [hW]; field_simp
  have hT0 : 0 ≤ T := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hσ : 1 + T + W < s.re := hs
  have hw1 := neg_abs_le w.re
  have hw2 := le_abs_self w.re
  have key1 : 1 + N + D.A₀ < s.re * d := by nlinarith
  have key2 : 1 + D.A₀ ≤ (s.re - 1) * d := by nlinarith
  have key3 : |w.re| < (s.re - 1) * m := by nlinarith
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.neg_re,
    zero_mul, sub_zero, mul_neg]
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem differentiable_G : Differentiable ℂ fun s => D.A s + D.At (1 - s) :=
  D.differentiable_A.add (D.differentiable_At.comp (differentiable_const _ |>.sub differentiable_id))

theorem differentiable_Gd : Differentiable ℂ fun s => D.At s + D.A (1 - s) :=
  D.differentiable_At.add (D.differentiable_A.comp (differentiable_const _ |>.sub differentiable_id))

theorem bounded_G (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
    ‖D.A s + D.At (1 - s)‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := D.bounded_A a b
  obtain ⟨C₂, hC₂0, hC₂⟩ := D.bounded_At (1 - b) (1 - a)
  refine ⟨C₁ + C₂, by positivity, fun s ha hb => (norm_add_le _ _).trans (add_le_add
    (hC₁ s ha hb) (hC₂ (1 - s) ?_ ?_))⟩
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · simp only [Complex.sub_re, Complex.one_re]; linarith

theorem ideleChar_inv_eq {w : ℂ} (hw : ∀ z, ideleChar F D.χ z = detPower F 1 z w) (z : Points F 1) :
    ideleChar F D.χ⁻¹ z = detPower F 1 z (-w) := by
  rw [ideleChar_inv, hw, detPower_one_eq, detPower_one_eq, ← Complex.exp_neg, neg_mul]

/-- **The main theorem for `EqualData`.** -/
theorem main : ∃ σ₀ : ℝ, ∃ I Idual : ℂ → ℂ,
    (∀ s : ℂ, σ₀ < s.re →
      ∫⁻ x, thetaKernelNorm F r D.P D.Φ s (Quotient.out x) ∂μq < ⊤ ∧
      ∫⁻ x, thetaKernelNorm F r D.Pd D.Φh s (Quotient.out x) ∂μq < ⊤ ∧
      I s = ∫ x, thetaKernel F r D.P D.Φ s (Quotient.out x) ∂μq ∧
      Idual s = ∫ x, thetaKernel F r D.Pd D.Φh s (Quotient.out x) ∂μq) ∧
    HasAtMostSimplePolesIn I (equalPoleSet F (r + 1) D.χ) ∧
    HasAtMostSimplePolesIn Idual (equalPoleSet F (r + 1) D.χ⁻¹) ∧
    BoundedInVerticalStripsAwayFrom I (equalPoleSet F (r + 1) D.χ) ∧
    ∀ s : ℂ, I s = Idual (1 - s) := by
  set n : ℂ := ((r + 1 : ℕ) : ℂ) with hndef
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
  rcases ideleChar_dichotomy F D.χ with ⟨w, hw⟩ | ⟨z₀, hz₀, hχ⟩
  · set C := residueConstant F r D.P w
    have hw' : ∀ z : Points F 1, (Automorphic.centralIdeleCharacter F D.χ (ideleOf F z) : ℂ) =
        detPower F 1 z w := hw
    have hwi : ∀ z : Points F 1, (Automorphic.centralIdeleCharacter F D.χ⁻¹ (ideleOf F z) : ℂ) =
        detPower F 1 z (-w) := D.ideleChar_inv_eq hw
    have hI : (fun s => D.A s + D.At (1 - s) + D.Φh 0 * (C / (n * (s - 1) + w)) -
        D.Φ 0 * (C / (n * s + w))) = fun s => (D.A s + D.At (1 - s)) +
          (D.Φh 0 * C) / (n * s + (w - n)) + (-(D.Φ 0 * C)) / (n * s + w) := by
      funext s
      rw [show n * (s - 1) + w = n * s + (w - n) by ring]
      ring
    have hId : (fun s => D.At s + D.A (1 - s) + D.Φ 0 * (-C / (n * (1 - s) + w)) -
        D.Φh 0 * (-C / (n * -s + w))) = fun s => (D.At s + D.A (1 - s)) +
          (D.Φh 0 * C) / (-n * s + w) + (-(D.Φ 0 * C)) / (-n * s + (n + w)) := by
      funext s
      rw [show n * (1 - s) + w = -n * s + (n + w) by ring, show n * -s + w = -n * s + w by ring]
      ring
    have m₁ : -(w - n) / n ∈ equalPoleSet F (r + 1) D.χ :=
      ⟨w, hw', Or.inr (by field_simp; ring)⟩
    have m₂ : -w / n ∈ equalPoleSet F (r + 1) D.χ := ⟨w, hw', Or.inl rfl⟩
    have m₃ : -w / -n ∈ equalPoleSet F (r + 1) D.χ⁻¹ :=
      ⟨-w, hwi, Or.inl (by rw [neg_div_neg_eq, neg_neg])⟩
    have m₄ : -(n + w) / -n ∈ equalPoleSet F (r + 1) D.χ⁻¹ :=
      ⟨-w, hwi, Or.inr (by field_simp; ring)⟩
    refine ⟨D.σ₀ w, fun s => D.A s + D.At (1 - s) + D.Φh 0 * (C / (n * (s - 1) + w)) -
        D.Φ 0 * (C / (n * s + w)),
      fun s => D.At s + D.A (1 - s) + D.Φ 0 * (-C / (n * (1 - s) + w)) -
        D.Φh 0 * (-C / (n * -s + w)), fun s hs => ?_, ?_, ?_, ?_, fun s => ?_⟩
    · obtain ⟨k1, k2, r1, r2, r3, r4, c1, c2, c3, c4⟩ := D.conditions w s hs
      refine ⟨D.lintegral_kernel_lt_top k1, D.lintegral_dual_kernel_lt_top k2, ?_, ?_⟩
      · rw [D.integral_kernel_eq s (D.integrable_resLt r1) (D.integrable_resLt r2),
          residueLt_eq_of_char D.hPc D.hPr D.hcent hw c1 (D.integrable_resLt r1),
          residueLt_eq_of_char D.hPc D.hPr D.hcent hw c2 (D.integrable_resLt r2)]
      · rw [D.integral_dual_kernel_eq s (D.integrable_resGe r3) (D.integrable_resGe r4),
          residueGe_eq_of_char D.hPc D.hPr D.hcent hw c3 (D.integrable_resGe r3),
          residueGe_eq_of_char D.hPc D.hPr D.hcent hw c4 (D.integrable_resGe r4)]
    · rw [hI]
      exact hasAtMostSimplePolesIn_two D.differentiable_G hn m₁ m₂
    · rw [hId]
      exact hasAtMostSimplePolesIn_two D.differentiable_Gd (neg_ne_zero.2 hn) m₃ m₄
    · rw [hI]
      exact boundedInVerticalStripsAwayFrom_two D.bounded_G hn m₁ m₂
    · simp only [sub_sub_cancel]
      rw [show n * -(1 - s) + w = n * (s - 1) + w by ring]
      ring
  · refine ⟨D.σ₀ 0, fun s => D.A s + D.At (1 - s), fun s => D.At s + D.A (1 - s),
      fun s hs => ?_, hasAtMostSimplePolesIn_entire D.differentiable_G _,
      hasAtMostSimplePolesIn_entire D.differentiable_Gd _,
      boundedInVerticalStripsAwayFrom_entire D.bounded_G _, fun s => ?_⟩
    · obtain ⟨k1, k2, r1, r2, r3, r4, -, -, -, -⟩ := D.conditions 0 s hs
      refine ⟨D.lintegral_kernel_lt_top k1, D.lintegral_dual_kernel_lt_top k2, ?_, ?_⟩
      · rw [D.integral_kernel_eq s (D.integrable_resLt r1) (D.integrable_resLt r2),
          residueLt_eq_zero D.hPc D.hPr D.hcent hz₀ hχ _ (D.integrable_resLt r1),
          residueLt_eq_zero D.hPc D.hPr D.hcent hz₀ hχ _ (D.integrable_resLt r2)]
        ring
      · rw [D.integral_dual_kernel_eq s (D.integrable_resGe r3) (D.integrable_resGe r4),
          residueGe_eq_zero D.hPc D.hPr D.hcent hz₀ hχ _ (D.integrable_resGe r3),
          residueGe_eq_zero D.hPc D.hPr D.hcent hz₀ hχ _ (D.integrable_resGe r4)]
        ring
    · simp only [sub_sub_cancel]
      ring

end EqualData

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
