import Langlands.Representation.Archimedean.RealMixedSwapSigned
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Right derivatives under the signed rank-three reversal -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean.RealMixedSwapTwist

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The real-linear direction change induced by inverse transpose. -/
def reverseDirection : A →ₗ[ℝ] A :=
  -(Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toLinearMap

@[simp] theorem reverseDirection_apply (X : A) : reverseDirection X = -Xᵀ := rfl

theorem reverseDirection_involutive : Function.Involutive reverseDirection := by
  intro X
  simp only [reverseDirection_apply, Matrix.transpose_neg, Matrix.transpose_transpose,
    neg_neg]

/-- Pullback by inverse transpose changes the right tangent direction to `-Xᵀ`. -/
theorem rightDerivative_twistLin {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) (X : A) (g : G) :
    rightDerivative (matrixModel ℝ 3) X (twistLin f) g =
      rightDerivative (matrixModel ℝ 3) (-Xᵀ) f (twist g) := by
  let T : A →L[ℝ] A :=
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toContinuousLinearEquiv
  let B : A → A := fun Y => wMat * (Ring.inverse Y)ᵀ
  have hBg : B (g : A) = (twist g : A) := by
    simp only [B, twist, theta_apply, Units.val_mul, w_val]
    rw [Ring.inverse_unit]
    rfl
  have hBd := ((T.hasFDerivAt.comp (g : A)
    (hasFDerivAt_ringInverse (𝕜 := ℝ) g)).const_mul wMat)
  change HasFDerivAt B _ (g : A) at hBd
  have hev : unitsExtension (twistLin f) =ᶠ[nhds (g : A)] unitsExtension f ∘ B := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with y hy
    obtain ⟨u, rfl⟩ := hy
    rw [unitsExtension_val, Function.comp_apply]
    change f (twist u) = unitsExtension f (B (u : A))
    have hBu : B (u : A) = (twist u : A) := by
      simp only [B, twist, theta_apply, Units.val_mul, w_val]
      rw [Ring.inverse_unit]
      rfl
    rw [hBu, unitsExtension_val]
  have hE : DifferentiableAt ℝ (unitsExtension f) (B (g : A)) := by
    rw [hBg]
    exact differentiableAt_unitsExtension hf (Units.isUnit _)
  rw [rightDerivative_eq_fderiv (contMDiff_twistLin hf), rightDerivative_eq_fderiv hf,
    hev.fderiv_eq, fderiv_comp _ hE hBd.differentiableAt, hBd.fderiv,
    ContinuousLinearMap.comp_apply, hBg]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  change wMat * (-((g⁻¹ : G).val * ((g : A) * X) * (g⁻¹ : G).val))ᵀ =
    (twist g : A) * -Xᵀ
  have hcancel : (g⁻¹ : G).val * ((g : A) * X) = X := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcancel]
  simp only [Matrix.transpose_mul, Matrix.transpose_neg, mul_neg, mul_assoc,
    twist, theta_apply, Units.val_mul, w_val, ← transposeGL_inv, transposeGL_val]

/-- The determinant sign is locally constant in matrix coordinates at any unit. -/
theorem eventually_signDet_ratio (g : G) :
    (fun Y : A => ((Y.det / |Y.det| : ℝ) : ℂ)) =ᶠ[nhds (g : A)]
      fun _ => signDet g := by
  have hdet : (g : A).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (g : A)).mp (Units.isUnit g)).ne_zero
  have hd : ContinuousAt (fun Y : A => Y.det) (g : A) :=
    continuous_id.matrix_det.continuousAt
  rcases lt_or_gt_of_ne hdet with hn | hp
  · filter_upwards [hd.eventually (gt_mem_nhds hn)] with Y hY
    simp only [signDet, abs_of_neg hn, abs_of_neg hY, div_neg,
      div_self hdet, div_self (ne_of_lt hY)]
  · filter_upwards [hd.eventually (lt_mem_nhds hp)] with Y hY
    simp only [signDet, abs_of_pos hp, abs_of_pos hY,
      div_self hdet, div_self (ne_of_gt hY)]

/-- The determinant-sign power contributes no term to the right derivative. -/
theorem rightDerivative_signedTwistLin (q : ℕ) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) (X : A) (g : G) :
    rightDerivative (matrixModel ℝ 3) X (signedTwistLin q f) g =
      signDet g ^ q * rightDerivative (matrixModel ℝ 3) (-Xᵀ) f (twist g) := by
  have hev : unitsExtension (signedTwistLin q f) =ᶠ[nhds (g : A)]
      fun Y => signDet g ^ q * unitsExtension (twistLin f) Y := by
    filter_upwards [eventually_signDet_ratio g,
      isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with Y hY hU
    obtain ⟨u, rfl⟩ := hU
    rw [unitsExtension_val, unitsExtension_val]
    change signDet u ^ q * f (twist u) = signDet g ^ q * f (twist u)
    rw [show signDet u = signDet g from hY]
  rw [rightDerivative_eq_fderiv (contMDiff_signedTwistLin q hf), hev.fderiv_eq,
    fderiv_const_mul (differentiableAt_unitsExtension (contMDiff_twistLin hf)
      (Units.isUnit g))]
  change signDet g ^ q *
      fderiv ℝ (unitsExtension (twistLin f)) (g : A) ((g : A) * X) = _
  rw [← rightDerivative_eq_fderiv (contMDiff_twistLin hf), rightDerivative_twistLin hf]

/-- Function-valued form of the signed derivative transport identity. -/
theorem rightDerivative_signedTwistLin_eq (q : ℕ) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) (X : A) :
    rightDerivative (matrixModel ℝ 3) X (signedTwistLin q f) =
      signedTwistLin q (rightDerivative (matrixModel ℝ 3) (-Xᵀ) f) := by
  funext g
  exact rightDerivative_signedTwistLin q hf X g

/-- Equivalent transport identity with the signed pullback on the derivative. -/
theorem signedTwistLin_rightDerivative (q : ℕ) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) (X : A) :
    signedTwistLin q (rightDerivative (matrixModel ℝ 3) X f) =
      rightDerivative (matrixModel ℝ 3) (reverseDirection X) (signedTwistLin q f) := by
  rw [rightDerivative_signedTwistLin_eq q hf]
  simp only [reverseDirection_apply, Matrix.transpose_neg, Matrix.transpose_transpose,
    neg_neg]

end Langlands.Archimedean.RealMixedSwapTwist
