import Langlands.Geometry.Manifold.LinearLieGroup.Exponential
import Langlands.Representation.Archimedean.RealInductionStagesDerivative
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-! # A quantitative skew logarithm near the orthogonal identity -/

noncomputable section

open Filter Set NormedSpace
open scoped Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LinearLieGroup

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

/-- Every orthogonal matrix sufficiently close to the identity is the exponential of a
skew-adjoint matrix whose norm is at most twice the displacement from the identity. -/
def OrthogonalLocalLogarithmStatement : Prop :=
  ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ k : O n, ‖(k : M n) - 1‖ < r →
    ∃ X : M n, star X = -X ∧ exp X = (k : M n) ∧ ‖X‖ ≤ 2 * ‖(k : M n) - 1‖

private theorem eventually_norm_le_twice_exp_sub_one (n : ℕ) :
    ∀ᶠ X : M n in 𝓝 0, ‖X‖ ≤ 2 * ‖exp X - 1‖ := by
  have hd := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := M n)).isLittleO.def (c := 1 / 2)
    (by norm_num)
  have hbound : ∀ᶠ X : M n in 𝓝 0, ‖exp X - 1 - X‖ ≤ (1 / 2 : ℝ) * ‖X‖ := by
    simpa only [exp_zero, one_apply_eq_self, sub_zero] using hd
  filter_upwards [hbound] with X hX
  have h : ‖X‖ ≤ ‖exp X - 1‖ + (1 / 2 : ℝ) * ‖X‖ := calc
    ‖X‖ = ‖(exp X - 1) - ((exp X - 1) - X)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖exp X - 1‖ + ‖(exp X - 1) - X‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl hX
  linarith

/-- Use the inverse function theorem at zero. Orthogonality equates the exponentials of
the adjoint and of the negative, so local injectivity makes the logarithm skew. -/
theorem orthogonalLocalLogarithm : OrthogonalLocalLogarithmStatement := by
  intro n
  let e := expPartialHomeomorph (M n)
  have h0 : (0 : M n) ∈ e.source := zero_mem_expPartialHomeomorph_source (M n)
  have h1 : (1 : M n) ∈ e.target := one_mem_expPartialHomeomorph_target (M n)
  have hsource : e.source ∈ 𝓝 (0 : M n) := e.open_source.mem_nhds h0
  have htarget : e.target ∈ 𝓝 (1 : M n) := e.open_target.mem_nhds h1
  have hstar : Tendsto (star : M n → M n) (𝓝 0) (𝓝 0) := by
    simpa only [star_zero] using (continuous_star.tendsto (0 : M n))
  have hneg : Tendsto (fun X : M n => -X) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : M n))
  have hl : Tendsto e.symm (𝓝 1) (𝓝 (0 : M n)) := by
    simpa only [expPartialHomeomorph_symm_one, e] using (e.continuousAt_symm h1).tendsto
  have hnear : ∀ᶠ k : M n in 𝓝 1, k ∈ e.target ∧ star (e.symm k) ∈ e.source ∧
      -e.symm k ∈ e.source ∧ ‖e.symm k‖ ≤ 2 * ‖exp (e.symm k) - 1‖ := by
    filter_upwards [htarget, (hstar.comp hl).eventually hsource,
      (hneg.comp hl).eventually hsource, hl.eventually (eventually_norm_le_twice_exp_sub_one n)]
      with k hkt hks hkn hkb
    exact ⟨hkt, hks, hkn, hkb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, fun k hk => ?_⟩
  obtain ⟨hkt, hks, hkn, hkb⟩ := hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hk)
  let X := e.symm (k : M n)
  have hX : exp X = (k : M n) := e.right_inv hkt
  refine ⟨X, ?_, hX, by simpa only [X, hX] using hkb⟩
  have hinv : (k : M n) * exp (-X) = 1 := by
    rw [← hX, ← exp_add_of_commute' (Commute.neg_right (Commute.refl X)),
      add_neg_cancel, exp_zero]
  have hkstar : star (k : M n) = exp (-X) := calc
    star (k : M n) = star (k : M n) * ((k : M n) * exp (-X)) := by rw [hinv, mul_one]
    _ = (star (k : M n) * (k : M n)) * exp (-X) := by rw [mul_assoc]
    _ = exp (-X) := by rw [Unitary.star_mul_self_of_mem k.prop, one_mul]
  apply e.injOn hks hkn
  change exp (star X) = exp (-X)
  rw [← star_exp, hX, hkstar]

private theorem expCurve_add {n : ℕ} (X : M n) (hX : Xᵀ = -X) (t s : ℝ) :
    InductionStages.expCurve X hX (t + s) =
      InductionStages.expCurve X hX t * InductionStages.expCurve X hX s := by
  apply Subtype.ext
  change exp ((t + s) • X) = exp (t • X) * exp (s • X)
  rw [add_smul, exp_add_of_commute' (((Commute.refl X).smul_left t).smul_right s)]

private theorem norm_sub_le_of_skew_curve {n : ℕ} (f : C(O n, ℂ)) {D : ℝ}
    (hD : ∀ (x : O n) (X : M n) (hX : Xᵀ = -X), ∃ a : ℂ,
      HasDerivAt (fun s : ℝ => f (x * InductionStages.expCurve X hX s)) a 0 ∧
        ‖a‖ ≤ D * ‖X‖)
    (x : O n) (X : M n) (hX : Xᵀ = -X) :
    ‖f (x * InductionStages.expCurve X hX 1) - f x‖ ≤ D * ‖X‖ := by
  let g (s : ℝ) := f (x * InductionStages.expCurve X hX s)
  have hd (t : ℝ) : ∃ a : ℂ, HasDerivAt g a t ∧ ‖a‖ ≤ D * ‖X‖ := by
    obtain ⟨a, ha, haD⟩ := hD (x * InductionStages.expCurve X hX t) X hX
    have h₀ : HasDerivAt (fun s : ℝ => f ((x * InductionStages.expCurve X hX t) *
        InductionStages.expCurve X hX s)) a (t - t) := by simpa only [sub_self] using ha
    have h₁ := h₀.comp_sub_const t t
    have he : (fun s : ℝ => f ((x * InductionStages.expCurve X hX t) *
        InductionStages.expCurve X hX (s - t))) = g := by
      funext s
      rw [mul_assoc, ← expCurve_add, add_sub_cancel]
    rw [he] at h₁
    exact ⟨a, h₁, haD⟩
  choose a ha haD using hd
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (ha t).hasDerivWithinAt) (fun t _ => haD t)
  simpa only [g, InductionStages.expCurve_zero, mul_one] using h

/-- A bound on right skew-direction derivatives and the supremum norm control global
Lipschitz continuity for the inherited matrix norm. The factor depends only on the rank. -/
theorem exists_lipschitz_bound_of_skew_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : C(O n, ℂ)) (D : ℝ), 0 ≤ D →
      (∀ (x : O n) (X : M n) (hX : Xᵀ = -X), ∃ a : ℂ,
        HasDerivAt (fun s : ℝ => f (x * InductionStages.expCurve X hX s)) a 0 ∧
          ‖a‖ ≤ D * ‖X‖) →
      ∀ x y : O n, ‖f y - f x‖ ≤ C * (‖f‖ + D) * ‖(y : M n) - (x : M n)‖ := by
  obtain ⟨r, hr, hlog⟩ := orthogonalLocalLogarithm n
  have hi : Continuous (fun x : O n => (↑(x⁻¹) : M n)) :=
    continuous_subtype_val.comp continuous_inv
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn hi.continuousOn
  let B := max 1 H
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hBnd (x : O n) : ‖(↑(x⁻¹) : M n)‖ ≤ B := (hH x (mem_univ x)).trans (le_max_right _ _)
  let C := max (2 * B) (2 * B / r)
  have hC : 0 < C := (by positivity : 0 < 2 * B).trans_le (le_max_left _ _)
  refine ⟨C, hC, fun f D hD₀ hD x y => ?_⟩
  let δ := ‖(y : M n) - (x : M n)‖
  have hδ : 0 ≤ δ := norm_nonneg _
  by_cases hsmall : δ < r / B
  · have hmatrix : (↑(x⁻¹ * y) : M n) - 1 = (↑(x⁻¹) : M n) * ((y : M n) - (x : M n)) := by
      rw [mul_sub, ← Submonoid.coe_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    have hdist : ‖(↑(x⁻¹ * y) : M n) - 1‖ ≤ B * δ := by
      rw [hmatrix]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hBnd x) hδ)
    have hδr : B * δ < r := by rw [mul_comm]; exact (lt_div_iff₀ hB).mp hsmall
    obtain ⟨X, hX, hXe, hXn⟩ := hlog (x⁻¹ * y) (hdist.trans_lt hδr)
    have hXt : Xᵀ = -X := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hX
    have h1 : InductionStages.expCurve X hXt 1 = x⁻¹ * y :=
      Subtype.ext (by simpa only [InductionStages.expCurve, one_smul] using hXe)
    have hnorm := norm_sub_le_of_skew_curve f hD x X hXt
    rw [h1, mul_inv_cancel_left] at hnorm
    have hXb : ‖X‖ ≤ 2 * (B * δ) := hXn.trans (mul_le_mul_of_nonneg_left hdist (by norm_num))
    calc
      _ ≤ D * ‖X‖ := hnorm
      _ ≤ D * (2 * (B * δ)) := mul_le_mul_of_nonneg_left hXb hD₀
      _ = (2 * B) * D * δ := by ring
      _ ≤ _ := by
        have hC₁ : 2 * B ≤ C := le_max_left _ _
        have hD₁ : D ≤ ‖f‖ + D := le_add_of_nonneg_left (norm_nonneg f)
        gcongr
  · have hrδ : r ≤ δ * B := (div_le_iff₀ hB).mp (le_of_not_gt hsmall)
    calc
      ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ 2 * ‖f‖ := by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y]
      _ ≤ (2 * B / r) * ‖f‖ * δ := by
        calc
          _ = (2 * ‖f‖ / r) * r := by field_simp
          _ ≤ (2 * ‖f‖ / r) * (δ * B) := mul_le_mul_of_nonneg_left hrδ (by positivity)
          _ = _ := by ring
      _ ≤ _ := by
        have hC₂ : 2 * B / r ≤ C := le_max_right _ _
        have hD₂ : ‖f‖ ≤ ‖f‖ + D := le_add_of_nonneg_right hD₀
        gcongr

end Langlands.Archimedean
