import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A norm comparison for the real rank-four exponent bound

This is the norm calculation in one spin-one column of the symmetric matrices.
The raising and lowering maps are adjoint, while the three real matrix actions
in the column are skew adjoint.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealRankFourNormComparison

open Complex
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem sqNorm_mul_le_of_inner {u y z : V} {r : ℂ} {c : ℝ}
    (hc : 0 ≤ c)
    (hinner : ⟪z, y⟫_ℂ = r * ⟪u, u⟫_ℂ)
    (hz : ‖z‖ ^ 2 = c * ‖u‖ ^ 2) :
    ‖r‖ ^ 2 * ‖u‖ ^ 2 ≤ c * ‖y‖ ^ 2 := by
  by_cases hu : u = 0
  · simpa [hu] using mul_nonneg hc (sq_nonneg ‖y‖)
  have hu_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have h := norm_inner_le_norm (𝕜 := ℂ) z y
  rw [hinner, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg u)] at h
  have hsq : (‖r‖ * ‖u‖ ^ 2) ^ 2 ≤ (‖z‖ * ‖y‖) ^ 2 := by
    gcongr
  rw [mul_pow, mul_pow, hz] at hsq
  apply (mul_le_mul_iff_left₀ hu_pos).mp
  calc
    (‖r‖ ^ 2 * ‖u‖ ^ 2) * ‖u‖ ^ 2 = ‖r‖ ^ 2 * (‖u‖ ^ 2) ^ 2 := by ring
    _ ≤ c * ‖u‖ ^ 2 * ‖y‖ ^ 2 := hsq
    _ = (c * ‖y‖ ^ 2) * ‖u‖ ^ 2 := by ring

/-- The squared norms of the two noncompact root actions differ by the
compact Cartan weight. -/
theorem normSq_sub_normSq_of_commutator
    (v : V) (P Q : Module.End ℂ V) (weight : ℝ)
    (hP : ∀ x y : V, ⟪P x, y⟫_ℂ = -⟪x, P y⟫_ℂ)
    (hQ : ∀ x y : V, ⟪Q x, y⟫_ℂ = -⟪x, Q y⟫_ℂ)
    (hcomm : ((P - I • Q) * (P + I • Q) - (P + I • Q) * (P - I • Q)) v =
      (weight : ℂ) • v) :
    ‖(P - I • Q) v‖ ^ 2 - ‖(P + I • Q) v‖ ^ 2 = weight * ‖v‖ ^ 2 := by
  let T := P - I • Q
  let S := P + I • Q
  change (T * S - S * T) v = (weight : ℂ) • v at hcomm
  change ‖T v‖ ^ 2 - ‖S v‖ ^ 2 = weight * ‖v‖ ^ 2
  have hTS (x y : V) : ⟪T x, y⟫_ℂ = -⟪x, S y⟫_ℂ := by
    simp only [T, S, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      inner_add_right, inner_sub_left, inner_smul_left, inner_smul_right, hP, hQ]
    change -⟪x, P y⟫_ℂ - star I * (-⟪x, Q y⟫_ℂ) =
      -(⟪x, P y⟫_ℂ + I * ⟪x, Q y⟫_ℂ)
    rw [show star I = -I from Complex.conj_I]
    ring
  have hST (x y : V) : ⟪S x, y⟫_ℂ = -⟪x, T y⟫_ℂ := by
    simp only [T, S, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      inner_sub_right, inner_add_left, inner_smul_left, inner_smul_right, hP, hQ]
    change -⟪x, P y⟫_ℂ + star I * (-⟪x, Q y⟫_ℂ) =
      -(⟪x, P y⟫_ℂ - I * ⟪x, Q y⟫_ℂ)
    rw [show star I = -I from Complex.conj_I]
    ring
  have h := congrArg (fun x : V => (⟪v, x⟫_ℂ).re) hcomm
  simp only [LinearMap.sub_apply, Module.End.mul_apply, inner_sub_right, inner_smul_right,
    sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
    ← inner_self_eq_norm_sq (𝕜 := ℂ), hTS v (T v), hST v (S v)]
  change (-⟪v, S (T v)⟫_ℂ).re - (-⟪v, T (S v)⟫_ℂ).re = weight * (⟪v, v⟫_ℂ).re
  rw [neg_re, neg_re]
  linarith

/-- In a spin-one column, the two successive compact lowering tests make the
three real squared norms at least `(weight/2 + 1) ‖v‖²`. The hypotheses record the
weights and raising identities for the three vectors `u`, `P₀ v`, `w`. -/
theorem columnEnergy_ge
    {weight : ℝ} (hweight : 0 < weight) (v u w y : V) (E F : Module.End ℂ V)
    (hadj : ∀ x z : V, ⟪F x, z⟫_ℂ = ⟪x, E z⟫_ℂ)
    (hF : E (F u) = ((weight + 2 : ℝ) : ℂ) • u)
    (hFF : E (F (F u)) = ((2 * (weight + 1) : ℝ) : ℂ) • F u)
    (hy : E y = -I • u) (hw : E (E w) = (2 : ℂ) • u)
    (hdiff : ‖u‖ ^ 2 - ‖w‖ ^ 2 = weight * ‖v‖ ^ 2) :
    (weight / 2 + 1) * ‖v‖ ^ 2 ≤ (‖u‖ ^ 2 + ‖w‖ ^ 2) / 2 + ‖y‖ ^ 2 := by
  have hre (x : V) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hFu : ‖F u‖ ^ 2 = (weight + 2) * ‖u‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, hF, inner_smul_right]
    change (↑(weight + 2 : ℝ) * ⟪u, u⟫_ℂ).re = (weight + 2) * ‖u‖ ^ 2
    rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hre]
  have hFFu : ‖F (F u)‖ ^ 2 = 2 * (weight + 1) * (weight + 2) * ‖u‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, hFF, inner_smul_right]
    change (↑(2 * (weight + 1) : ℝ) * ⟪F u, F u⟫_ℂ).re =
      2 * (weight + 1) * (weight + 2) * ‖u‖ ^ 2
    rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hre, hFu]
    ring
  have h1 : ‖u‖ ^ 2 ≤ (weight + 2) * ‖y‖ ^ 2 := by
    have ht := sqNorm_mul_le_of_inner (by positivity : 0 ≤ weight + 2)
      (by rw [hadj, hy, inner_smul_right]) hFu
    simpa using ht
  have h2 : 2 * ‖u‖ ^ 2 ≤ (weight + 1) * (weight + 2) * ‖w‖ ^ 2 := by
    have ht := sqNorm_mul_le_of_inner (by positivity : 0 ≤ 2 * (weight + 1) * (weight + 2))
      (by rw [hadj, hadj, hw, inner_smul_right]) hFFu
    norm_num at ht
    linarith only [ht]
  have hw_lower : 2 * ‖v‖ ^ 2 ≤ (weight + 3) * ‖w‖ ^ 2 := by
    apply (mul_le_mul_iff_left₀ hweight).mp
    calc
      (2 * ‖v‖ ^ 2) * weight = 2 * ‖u‖ ^ 2 - 2 * ‖w‖ ^ 2 := by
        linear_combination -2 * hdiff
      _ ≤ ((weight + 1) * (weight + 2) - 2) * ‖w‖ ^ 2 := by
        rw [sub_mul]
        exact sub_le_sub_right h2 _
      _ = ((weight + 3) * ‖w‖ ^ 2) * weight := by ring
  have hsum : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 + ‖y‖ ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < weight + 2 by positivity)).mp
    calc
      ‖v‖ ^ 2 * (weight + 2) = 2 * ‖v‖ ^ 2 + (‖u‖ ^ 2 - ‖w‖ ^ 2) := by
        linear_combination -hdiff
      _ ≤ (weight + 3) * ‖w‖ ^ 2 + ((weight + 2) * ‖y‖ ^ 2 - ‖w‖ ^ 2) :=
        add_le_add hw_lower (sub_le_sub_right h1 _)
      _ = (‖w‖ ^ 2 + ‖y‖ ^ 2) * (weight + 2) := by ring
  nlinarith only [hdiff, hsum]

end Langlands.Archimedean.RealRankFourNormComparison
