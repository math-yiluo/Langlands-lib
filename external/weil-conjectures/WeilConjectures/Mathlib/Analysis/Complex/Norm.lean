/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.LinearCombination

/-!
# Norms of complex numbers on a circle centred at the origin

If `‖z‖² = q⁻¹` for a positive real `q`, then `‖q⁻¹ - z‖² = q⁻¹ ‖1 - z‖²`: the inversion
`w ↦ q⁻¹ / w̄` in the circle of radius `q^{-1/2}` fixes `z` and exchanges `1` and `q⁻¹`.
-/

@[expose] public section

namespace Complex

/-- If `‖z‖² = q⁻¹`, then `‖q⁻¹ - z‖² = q⁻¹ ‖1 - z‖²`: both sides are
`q⁻¹ (q⁻¹ - 2 Re z + 1)`. -/
theorem sq_norm_inv_sub_eq {q : ℝ} {z : ℂ} (hz : ‖z‖ ^ 2 = q⁻¹) :
    ‖(q : ℂ)⁻¹ - z‖ ^ 2 = q⁻¹ * ‖1 - z‖ ^ 2 := by
  have hz2 : z.re ^ 2 + z.im ^ 2 = q⁻¹ := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [← Complex.ofReal_inv, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  linear_combination (1 - q⁻¹) * hz2

end Complex
