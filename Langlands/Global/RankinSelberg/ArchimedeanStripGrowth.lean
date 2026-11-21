import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds
import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Phragmén–Lindelöf for Gaussian regularization -/

noncomputable section

open Complex Set Asymptotics Filter
open scoped Topology Filter Real

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

/-- A norm bound by an exponential quadratic in the imaginary part on every finite vertical strip. -/
def StripQuadraticGrowth (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
    ‖F z‖ ≤ C * Real.exp (K * (1 + |z.im| ^ 2))

/-- The all-height exponential strip estimate implies the large-height version. -/
theorem StripExpType.hasStripExponentialGrowth {F : ℂ → ℂ} (hF : StripExpType F) :
    Langlands.LocalFactor.Archimedean.HasStripExponentialGrowth F := by
  intro a b
  obtain ⟨C, K, hC, hK, h⟩ := hF a b
  refine ⟨C, K, 0, hC, hK, fun z hz hz' _ => ?_⟩
  simpa only [re_add_im] using h z.re hz hz' z.im

private theorem norm_exp_mul_sq (e : ℝ) (z : ℂ) :
    ‖Complex.exp ((e : ℂ) * z ^ 2)‖ = Real.exp (e * (z.re ^ 2 - z.im ^ 2)) := by
  rw [norm_exp]
  congr 1
  simp [pow_two]

private theorem re_sq_le {a b : ℝ} {z : ℂ} (ha : a ≤ z.re) (hb : z.re ≤ b) :
    z.re ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_total 0 z.re with h | h <;> nlinarith

private theorem sq_le_doubleExp {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y ^ 2) ≤ (1 + 2 / c ^ 2) * Real.exp (c * y) := by
  have hE := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hy)
  have h₁ := Real.one_le_exp (mul_nonneg hc.le hy)
  have h₂ : y ^ 2 ≤ (2 / c ^ 2) * Real.exp (c * y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < c ^ 2 by positivity)).mpr
    nlinarith [mul_nonneg hc.le hy]
  rw [add_mul, one_mul]
  exact add_le_add h₁ h₂

private theorem damped_norm_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hQ : StripQuadraticGrowth F)
    {a b C K : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hBa : ∀ z : ℂ, z.re = a → ‖F z‖ ≤ C * Real.exp (K * |z.im|))
    (hBb : ∀ z : ℂ, z.re = b → ‖F z‖ ≤ C * Real.exp (K * |z.im|))
    {e : ℝ} (he : 0 < e) {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖F z * Complex.exp ((e : ℂ) * z ^ 2)‖ ≤ C * Real.exp (e * (a ^ 2 + b ^ 2) + K ^ 2 / (4 * e)) := by
  let H (s : ℂ) := F s * Complex.exp ((e : ℂ) * s ^ 2)
  have hH : Differentiable ℂ H := hF.mul ((differentiable_id.pow 2).const_mul (e : ℂ)).cexp
  have hBoundary (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b)
      (hbound : ‖F s‖ ≤ C * Real.exp (K * |s.im|)) :
      ‖H s‖ ≤ C * Real.exp (e * (a ^ 2 + b ^ 2) + K ^ 2 / (4 * e)) := by
    have hr := re_sq_le ha hb
    change ‖F s * Complex.exp ((e : ℂ) * s ^ 2)‖ ≤ _
    rw [norm_mul, norm_exp_mul_sq]
    calc
      _ ≤ (C * Real.exp (K * |s.im|)) * Real.exp (e * (s.re ^ 2 - s.im ^ 2)) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
      _ = C * Real.exp (e * s.re ^ 2 + (K * |s.im| - e * |s.im| ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add, sq_abs]
        congr 2
        ring
      _ ≤ _ := by
        have hY : K * |s.im| - e * |s.im| ^ 2 ≤ K ^ 2 / (4 * e) := by
          apply (le_div_iff₀ (show 0 < 4 * e by positivity)).mpr
          nlinarith only [sq_nonneg (2 * e * |s.im| - K)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (add_le_add (mul_le_mul_of_nonneg_left hr he.le) hY)) hC
  refine PhragmenLindelof.vertical_strip (f := H) (a := a) (b := b) hH.diffContOnCl ?_
    (fun s hs => hBoundary s hs.ge (hs.le.trans hab.le) (hBa s hs))
    (fun s hs => hBoundary s (hab.le.trans hs.ge) hs.le (hBb s hs)) hza hzb
  · obtain ⟨D, L, hD, hL, hQ⟩ := hQ a b
    let c := Real.pi / (2 * (b - a))
    have hwidth : 0 < b - a := sub_pos.mpr hab
    have hc : 0 < c := div_pos Real.pi_pos (by positivity)
    have hclt : c < Real.pi / (b - a) := by
      dsimp only [c]
      rw [mul_comm (2 : ℝ), ← div_div]
      linarith [div_pos Real.pi_pos hwidth]
    refine ⟨c, hclt, L * (1 + 2 / c ^ 2), IsBigO.of_bound (D * Real.exp (e * (a ^ 2 + b ^ 2))) ?_⟩
    have hStrip : ∀ᶠ s : ℂ in comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b), s ∈ re ⁻¹' Ioo a b :=
      Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr fun _ hs => hs)
    filter_upwards [hStrip] with s hs
    have hr := re_sq_le hs.1.le hs.2.le
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    change ‖F s * Complex.exp ((e : ℂ) * s ^ 2)‖ ≤ _
    rw [norm_mul, norm_exp_mul_sq]
    calc
      _ ≤ (D * Real.exp (L * (1 + |s.im| ^ 2))) * Real.exp (e * (a ^ 2 + b ^ 2)) := by
        refine mul_le_mul (hQ s hs.1.le hs.2.le) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hr he.le, mul_nonneg he.le (sq_nonneg s.im)]
      _ ≤ _ := by
        have hE := mul_le_mul_of_nonneg_left (sq_le_doubleExp hc (abs_nonneg s.im)) hL
        calc
          _ = (D * Real.exp (e * (a ^ 2 + b ^ 2))) * Real.exp (L * (1 + |s.im| ^ 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)

private theorem norm_le_of_boundary {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hQ : StripQuadraticGrowth F)
    {a b C K : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hBa : ∀ z : ℂ, z.re = a → ‖F z‖ ≤ C * Real.exp (K * |z.im|))
    (hBb : ∀ z : ℂ, z.re = b → ‖F z‖ ≤ C * Real.exp (K * |z.im|))
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖F z‖ ≤ (C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 4)) * Real.exp ((1 + K ^ 2 / 4) * |z.im|) := by
  let y := |z.im|
  let e := (1 + y)⁻¹
  have hy : 0 ≤ y := abs_nonneg _
  have he₀ : 0 < 1 + y := by positivity
  have he : 0 < e := inv_pos.mpr he₀
  have he₁ : e ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hq : K ^ 2 / (4 * e) = (K ^ 2 / 4) * (1 + y) := by
    change K ^ 2 / (4 * (1 + y)⁻¹) = _
    rw [div_mul_eq_div_div, div_inv_eq_mul]
  have hyy : e * z.im ^ 2 ≤ y := by
    change (1 + y)⁻¹ * z.im ^ 2 ≤ y
    rw [← sq_abs z.im, inv_mul_eq_div]
    exact (div_le_iff₀ he₀).mpr (by nlinarith)
  have h := damped_norm_le hF hQ hab hC hBa hBb he hza hzb
  rw [norm_mul, norm_exp_mul_sq] at h
  calc
    ‖F z‖ ≤ (C * Real.exp (e * (a ^ 2 + b ^ 2) + K ^ 2 / (4 * e))) /
        Real.exp (e * (z.re ^ 2 - z.im ^ 2)) := (le_div_iff₀ (Real.exp_pos _)).mpr h
    _ = C * Real.exp (e * (a ^ 2 + b ^ 2) + K ^ 2 / (4 * e) - e * (z.re ^ 2 - z.im ^ 2)) := by
      rw [Real.exp_sub, mul_div_assoc]
    _ ≤ C * Real.exp (a ^ 2 + b ^ 2 + K ^ 2 / 4 + (1 + K ^ 2 / 4) * y) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      rw [hq]
      nlinarith [mul_le_mul_of_nonneg_right he₁ (show 0 ≤ a ^ 2 + b ^ 2 by positivity),
        mul_nonneg he.le (sq_nonneg z.re)]
    _ = _ := by rw [Real.exp_add, mul_assoc]

/-- Entire functions of at most Gaussian growth inside strips are of exponential type when
all sufficiently far outside vertical lines have bounds of exponential type. -/
def ArchimedeanStripGrowthStatement : Prop :=
  ∀ (F : ℂ → ℂ), Differentiable ℂ F → StripQuadraticGrowth F →
    (∃ a b : ℝ, ∀ x : ℝ, x < a ∨ b < x → ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, z.re = x → ‖F z‖ ≤ C * Real.exp (K * |z.im|)) → StripExpType F

theorem archimedeanStripGrowth : ArchimedeanStripGrowthStatement := by
  intro F hF hQ hOutside a b
  obtain ⟨A, B, hO⟩ := hOutside
  let l := min a (min b A) - 1
  let r := max a (max b B) + 1
  have hla : l ≤ a := by dsimp only [l]; linarith [min_le_left a (min b A)]
  have hlA : l < A := by dsimp only [l]; linarith [min_le_right a (min b A), min_le_right b A]
  have hbr : b ≤ r := by dsimp only [r]; linarith [le_max_right a (max b B), le_max_left b B]
  have hBr : B < r := by dsimp only [r]; linarith [le_max_right a (max b B), le_max_right b B]
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hO l (.inl hlA)
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hO r (.inr hBr)
  let C := max C₁ C₂
  let K := max K₁ K₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have hK : 0 ≤ K := hK₁.trans (le_max_left _ _)
  have hleft (z : ℂ) (hz : z.re = l) : ‖F z‖ ≤ C * Real.exp (K * |z.im|) :=
    (h₁ z hz).trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (Real.exp_nonneg _) hC)
  have hright (z : ℂ) (hz : z.re = r) : ‖F z‖ ≤ C * Real.exp (K * |z.im|) :=
    (h₂ z hz).trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))) (Real.exp_nonneg _) hC)
  have hspan : l < r := by
    dsimp only [l, r]
    linarith [min_le_left a (min b A), le_max_left a (max b B)]
  refine ⟨C * Real.exp (l ^ 2 + r ^ 2 + K ^ 2 / 4), 1 + K ^ 2 / 4, by positivity, by positivity, fun x hx hx' y => ?_⟩
  have hz := norm_le_of_boundary hF hQ hspan hC hleft hright (z := (x : ℂ) + (y : ℂ) * I)
    (by simpa using hla.trans hx) (by simpa using hx'.trans hbr)
  simpa using hz

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
