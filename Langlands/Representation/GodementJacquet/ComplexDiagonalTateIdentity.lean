import Langlands.Representation.GodementJacquet.ComplexDiagonalZeta
import Langlands.Representation.GodementJacquet.ComplexCoordinateDilation

/-! # The two-test Tate identity on the product of common strips -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

variable {ι : Type*} [Fintype ι]
local notation "Z" => ι → ℂ

private def radialDirection (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

private theorem complexMellinWeight_mul (m : ℤ) (u : ℂ) {x : ℂ} (hx : x ≠ 0) (z : ℂ) :
    complexMellinWeight m u (x * z) =
      radialDirection x ^ m * (‖x‖ : ℂ) ^ (2 * u - 2) * complexMellinWeight m u z := by
  by_cases hz : z = 0
  · simp [hz, complexMellinWeight]
  simp only [complexMellinWeight, mul_ne_zero hx hz, hz, ite_false, radialDirection,
    norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg x) (norm_nonneg z)]
  ring

private theorem complexMellinWeight_jacobian (m : ℤ) (u : ℂ) {x : ℂ} (hx : x ≠ 0) (z : ℂ) :
    complexMellinWeight m u x * ((complexAbsHom x : ℝ) : ℂ) *
      complexMellinWeight (-m) (1 - u) (x * z) = complexMellinWeight (-m) (1 - u) z := by
  have hn : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hd₀ : radialDirection x ≠ 0 := div_ne_zero hx hn
  have hd : radialDirection x ^ m * radialDirection x ^ (-m) = 1 :=
    by rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hd₀)]
  have htwo : (‖x‖ : ℂ) ^ (2 : ℂ) = (‖x‖ : ℂ) ^ (2 : ℕ) := by
    exact mod_cast Complex.cpow_natCast (‖x‖ : ℂ) 2
  have hr : (‖x‖ : ℂ) ^ (2 * u - 2) * (‖x‖ : ℂ) ^ (2 * (1 - u) - 2) *
      (‖x‖ : ℂ) ^ (2 : ℕ) = 1 := by
    rw [← Complex.cpow_add _ _ hn,
      show 2 * u - 2 + (2 * (1 - u) - 2) = -(2 : ℂ) by ring,
      Complex.cpow_neg, htwo, inv_mul_cancel₀ (pow_ne_zero _ hn)]
  rw [complexMellinWeight_mul (-m) (1 - u) hx z,
    show complexMellinWeight m u x =
        radialDirection x ^ m * (‖x‖ : ℂ) ^ (2 * u - 2) by
      simp only [complexMellinWeight, ite_eq_right hx, radialDirection],
    coe_complexAbsHom, Complex.ofReal_pow]
  calc
    _ = (radialDirection x ^ m * radialDirection x ^ (-m)) *
        ((‖x‖ : ℂ) ^ (2 * u - 2) * (‖x‖ : ℂ) ^ (2 * (1 - u) - 2) *
          (‖x‖ : ℂ) ^ (2 : ℕ)) * complexMellinWeight (-m) (1 - u) z := by ring
    _ = _ := by rw [hd, hr, one_mul, one_mul]

private def dualWeight (m : ι → ℤ) (u : Z) (z : Z) : ℂ :=
  ∏ i, complexMellinWeight (-(m i)) (1 - u i) (z i)

private theorem measurable_dualWeight (m : ι → ℤ) (u : Z) :
    Measurable (dualWeight m u) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_complexMellinWeight (-(m i)) (1 - u i)).comp (measurable_pi_apply i)

private def diagonalProductKernel (Φ Ψ : Z → ℂ) (m : ι → ℤ) (u : Z) (x z : Z) : ℂ :=
  Φ x * Ψ (x * z) * dualWeight m u z

private theorem diagonalProductKernel_eq (Φ Ψ : Z → ℂ) (m : ι → ℤ) (u : Z)
    {x : Z} (hx : ∀ i, x i ≠ 0) (z : Z) :
    diagonalProductKernel Φ Ψ m u x z =
      complexDiagonalZetaKernel Φ m u x * ((complexCoordinateJacobian x : ℝ) : ℂ) *
        complexDiagonalZetaKernel Ψ (-m) (1 - u) (x * z) := by
  simp only [diagonalProductKernel, complexDiagonalZetaKernel, complexCoordinateJacobian,
    NNReal.coe_prod, Complex.ofReal_prod, Pi.neg_apply, Pi.sub_apply, Pi.one_apply, Pi.mul_apply]
  symm
  calc
    _ = Φ x * Ψ (x * z) *
        ∏ i, (complexMellinWeight (m i) (u i) (x i) * ((complexAbsHom (x i) : ℝ) : ℂ) *
          complexMellinWeight (-(m i)) (1 - u i) (x i * z i)) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := congrArg _ (Finset.prod_congr rfl fun i _ =>
      complexMellinWeight_jacobian (m i) (u i) (hx i) (z i))

private theorem integral_diagonalProductSlice (a : ℂˣ) (Φ Ψ : Z → ℂ) (m : ι → ℤ) (u : Z)
    {x : Z} (hx : ∀ i, x i ≠ 0) :
    (∫ z, diagonalProductKernel Φ Ψ m u x z ∂complexCoordinateMeasure ι a) =
      complexDiagonalZetaKernel Φ m u x *
        ∫ z, complexDiagonalZetaKernel Ψ (-m) (1 - u) z ∂complexCoordinateMeasure ι a := by
  simp_rw [diagonalProductKernel_eq Φ Ψ m u hx]
  rw [integral_const_mul, integral_complexCoordinateDilation a x hx, Complex.real_smul]
  have h : ((complexCoordinateJacobian x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast complexCoordinateJacobian_ne_zero hx
  simp only [Complex.ofReal_inv, mul_assoc, mul_inv_cancel_left₀ h]

private theorem integral_norm_diagonalProductSlice (a : ℂˣ) (Φ Ψ : Z → ℂ)
    (m : ι → ℤ) (u : Z) {x : Z} (hx : ∀ i, x i ≠ 0) :
    (∫ z, ‖diagonalProductKernel Φ Ψ m u x z‖ ∂complexCoordinateMeasure ι a) =
      ‖complexDiagonalZetaKernel Φ m u x‖ *
        ∫ z, ‖complexDiagonalZetaKernel Ψ (-m) (1 - u) z‖ ∂complexCoordinateMeasure ι a := by
  simp_rw [diagonalProductKernel_eq Φ Ψ m u hx, norm_mul, Complex.norm_of_nonneg
    (NNReal.coe_nonneg (complexCoordinateJacobian x))]
  rw [integral_const_mul, integral_complexCoordinateDilation a x hx
    (fun y => ‖complexDiagonalZetaKernel Ψ (-m) (1 - u) y‖), smul_eq_mul]
  have h : (complexCoordinateJacobian x : ℝ) ≠ 0 := by
    exact_mod_cast complexCoordinateJacobian_ne_zero hx
  simp only [mul_assoc, mul_inv_cancel_left₀ h]

private theorem diagonalZeta_mul_diagonalZeta_eq (a : ℂˣ) (Φ Ψ : SchwartzMap Z ℂ)
    (m : ι → ℤ) {u : Z} (hu₀ : ∀ i, 0 < (u i).re) (hu₁ : ∀ i, (u i).re < 1) :
    complexDiagonalZeta a Φ m u * complexDiagonalZeta a Ψ (-m) (1 - u) =
      ∫ z, (∫ x, Φ x * Ψ (x * z) ∂complexCoordinateMeasure ι a) *
        dualWeight m u z ∂complexCoordinateMeasure ι a := by
  let μ := complexCoordinateMeasure ι a
  have hv (i : ι) : 0 < ((1 - u) i).re := by
    simpa only [Pi.sub_apply, Pi.one_apply, Complex.sub_re, Complex.one_re] using sub_pos.mpr (hu₁ i)
  have hΦ := integrable_complexDiagonalZetaKernel a Φ m hu₀
  have hΨ := integrable_complexDiagonalZetaKernel a Ψ (-m) hv
  let F (x z : Z) := diagonalProductKernel Φ Ψ m u x z
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) :=
    (((Φ.continuous.measurable.comp measurable_fst).mul
      (Ψ.continuous.measurable.comp (measurable_fst.mul measurable_snd))).mul
        ((measurable_dualWeight m u).comp measurable_snd)).aestronglyMeasurable
  have hI : Integrable (Function.uncurry F) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨(ae_complexCoordinate_ne_zero a).mono (fun x hx => ?_), ?_⟩
    · change Integrable (fun z => diagonalProductKernel Φ Ψ m u x z) μ
      simp_rw [diagonalProductKernel_eq Φ Ψ m u hx]
      exact (integrable_complexCoordinateDilation a x hx hΨ).const_mul _
    · exact (hΦ.norm.mul_const (∫ z, ‖complexDiagonalZetaKernel Ψ (-m) (1 - u) z‖ ∂μ)).congr
        ((ae_complexCoordinate_ne_zero a).mono fun x hx =>
          (integral_norm_diagonalProductSlice a Φ Ψ m u hx).symm)
  rw [complexDiagonalZeta_eq_integral a Φ m hu₀, complexDiagonalZeta_eq_integral a Ψ (-m) hv]
  calc
    _ = ∫ x, (∫ z, F x z ∂μ) ∂μ := by
      rw [← integral_mul_const]
      exact integral_congr_ae ((ae_complexCoordinate_ne_zero a).mono fun x hx =>
        (integral_diagonalProductSlice a Φ Ψ m u hx).symm)
    _ = ∫ z, (∫ x, F x z ∂μ) ∂μ := integral_integral_swap hI
    _ = _ := integral_congr_ae (Eventually.of_forall fun z => integral_mul_const _ _)

private theorem complexCoordinatePair_mul_swap (x w z : Z) :
    complexCoordinatePair w (x * z) = complexCoordinatePair x (w * z) := by
  unfold complexCoordinatePair
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring

private theorem integral_mul_complexCoordinateFourier_mul (a : ℂˣ)
    (Φ Ψ : SchwartzMap Z ℂ) (z : Z) :
    (∫ x, Φ x * complexCoordinateFourier a Ψ (x * z) ∂complexCoordinateMeasure ι a) =
      ∫ w, Ψ w * complexCoordinateFourier a Φ (w * z) ∂complexCoordinateMeasure ι a := by
  let μ := complexCoordinateMeasure ι a
  let F (x w : Z) := Φ x * (Ψ w * traceCharacter a (complexCoordinatePair w (x * z)))
  have hpair : Continuous (fun p : Z × Z => complexCoordinatePair p.2 (p.1 * z)) := by
    unfold complexCoordinatePair
    simp only [Pi.mul_apply]
    fun_prop
  have hcont : Continuous (Function.uncurry F) :=
    (Φ.continuous.comp continuous_fst).mul ((Ψ.continuous.comp continuous_snd).mul
      ((continuous_traceCharacter a).comp hpair))
  have hI : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine ((Φ.integrable (μ := μ)).norm.mul_prod (Ψ.integrable (μ := μ)).norm).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => le_of_eq ?_)
    simp only [F, Function.uncurry, norm_mul, norm_traceCharacter, mul_one]
  calc
    _ = ∫ x, (∫ w, F x w ∂μ) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [F, μ, complexCoordinateFourier, integral_const_mul]
    _ = ∫ w, (∫ x, F x w ∂μ) ∂μ := integral_integral_swap hI
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        change (∫ x, F x w ∂μ) = Ψ w * complexCoordinateFourier a Φ (w * z)
        rw [complexCoordinateFourier, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [F, complexCoordinatePair_mul_swap x w z]
          ring

/-- The cross-multiplied Tate identity for two arbitrary Schwartz tests in all
coordinates on the product of the common strips. -/
theorem complexDiagonalTateIdentity (a : ℂˣ) (Φ Ψ Φf Ψf : SchwartzMap Z ℂ)
    (hΦ : (Φf : Z → ℂ) = complexCoordinateFourier a Φ)
    (hΨ : (Ψf : Z → ℂ) = complexCoordinateFourier a Ψ)
    (m : ι → ℤ) {u : Z} (hu₀ : ∀ i, 0 < (u i).re) (hu₁ : ∀ i, (u i).re < 1) :
    complexDiagonalZeta a Φ m u * complexDiagonalZeta a Ψf (-m) (1 - u) =
      complexDiagonalZeta a Φf (-m) (1 - u) * complexDiagonalZeta a Ψ m u := by
  rw [diagonalZeta_mul_diagonalZeta_eq a Φ Ψf m hu₀ hu₁,
    mul_comm (complexDiagonalZeta a Φf (-m) (1 - u)),
    diagonalZeta_mul_diagonalZeta_eq a Ψ Φf m hu₀ hu₁]
  apply integral_congr_ae
  refine Eventually.of_forall fun z => ?_
  simp only [hΦ, hΨ, integral_mul_complexCoordinateFourier_mul a Φ Ψ z]

end Langlands.GodementJacquet
