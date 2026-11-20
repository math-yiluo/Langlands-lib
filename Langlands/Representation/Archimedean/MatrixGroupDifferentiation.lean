import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.TransposePairingRestriction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Differentiation from continuous derivatives along matrix exponentials -/

noncomputable section

open Filter Set Metric
open scoped ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.MatrixGroupDifferentiation

variable {n : ℕ}
local notation "Square" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ

/-- Left multiplication by an invertible matrix, in real matrix coordinates. -/
def leftMul (g : G) : Square ≃L[ℝ] Square where
  toFun X := g.val * X
  invFun X := g⁻¹.val * X
  left_inv X := by
    change g⁻¹.val * (g.val * X) = X
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv X := by
    change g.val * (g⁻¹.val * X) = X
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' X Y := mul_add g.val X Y
  map_smul' c X := Matrix.mul_smul g.val c X
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

@[simp] theorem leftMul_apply (g : G) (X : Square) : leftMul g X = g.val * X := rfl

@[simp] theorem leftMul_symm_apply (g : G) (X : Square) : (leftMul g).symm X = g⁻¹.val * X := rfl

@[simp] theorem matrixExponentialGL_zero : matrixExponentialGL ℂ n (0 : Square) = 1 :=
  Units.ext NormedSpace.exp_zero

theorem continuous_matrixExponentialGL : Continuous (matrixExponentialGL ℂ n) :=
  Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr NormedSpace.exp_continuous

private theorem hasFDerivAt_exponentialCoordinates {F : G → ℂ} {D : G → Square →L[ℝ] ℂ}
    (hD : Continuous D)
    (hcurve : ∀ (g : G) (X : Square) (t : ℝ),
      HasDerivAt (fun u : ℝ => F (g * matrixExponentialGL ℂ n (u • X)))
        (D (g * matrixExponentialGL ℂ n (t • X)) X) t)
    (g : G) : HasFDerivAt (fun X : Square => F (g * matrixExponentialGL ℂ n X)) (D g) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  have hc : Continuous (fun X : Square => ‖D (g * matrixExponentialGL ℂ n X) - D g‖) :=
    ((hD.comp (continuous_const.mul continuous_matrixExponentialGL)).sub continuous_const).norm
  have he : ∀ᶠ X in 𝓝 (0 : Square), ‖D (g * matrixExponentialGL ℂ n X) - D g‖ < ε :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp he
  have hδ' : ∀ᶠ X in 𝓝 (0 : Square), X ∈ ball (0 : Square) δ := ball_mem_nhds _ hδ
  refine hδ'.mono fun X hX => ?_
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖D (g * matrixExponentialGL ℂ n (t • X)) X - D g X‖ ≤ ε * ‖X‖ := by
    have hsmall : t • X ∈ ball (0 : Square) δ := by
      rw [mem_ball, dist_zero_right] at hX ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg X) ht.2).trans_lt hX
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb hsmall).le (norm_nonneg _))
  let e := (fun t : ℝ => F (g * matrixExponentialGL ℂ n (t • X))) - (fun t : ℝ => t • D g X)
  have hd (t : ℝ) : HasDerivAt e (D (g * matrixExponentialGL ℂ n (t • X)) X - D g X) t := by
    simpa only [e, id_eq, one_smul] using
      (hcurve g X t).sub ((hasDerivAt_id t).smul_const (D g X))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => hbound t (Ico_subset_Icc_self ht))
  simpa only [e, Pi.sub_apply, one_smul, zero_smul, sub_zero, matrixExponentialGL_zero, mul_one,
    sub_right_comm] using hm

/-- Continuous right-trivialized derivatives along one-parameter matrix subgroups determine
an ambient Fréchet derivative on the invertible locus. -/
theorem hasFDerivAt_unitsExtension {F : G → ℂ} {D : G → Square →L[ℝ] ℂ}
    (hD : Continuous D)
    (hcurve : ∀ (g : G) (X : Square) (t : ℝ),
      HasDerivAt (fun u : ℝ => F (g * matrixExponentialGL ℂ n (u • X)))
        (D (g * matrixExponentialGL ℂ n (t • X)) X) t)
    (g : G) : HasFDerivAt (unitsExtension F)
      ((D g).comp (leftMul g).symm.toContinuousLinearMap) g.val := by
  let e (X : Square) := (g * matrixExponentialGL ℂ n X).val
  let L := leftMul g
  have he : HasStrictFDerivAt e L.toContinuousLinearMap 0 := by
    change HasStrictFDerivAt (fun X => L (NormedSpace.exp X)) L.toContinuousLinearMap 0
    have h := L.toContinuousLinearMap.hasStrictFDerivAt.comp (0 : Square)
      (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Square))
    change HasStrictFDerivAt _ (L.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ Square)) _ at h
    rwa [ContinuousLinearMap.comp_id] at h
  have he₀ : e 0 = g.val := by simp [e]
  let inv := he.localInverse e L 0
  have hinv : HasFDerivAt inv L.symm.toContinuousLinearMap g.val := by
    rw [← he₀]
    exact he.to_localInverse.hasFDerivAt
  have hinv₀ : inv g.val = 0 := by
    rw [← he₀]
    exact he.localInverse_apply_image
  have hc : HasFDerivAt (fun X : Square => F (g * matrixExponentialGL ℂ n X)) (D g) (inv g.val) := by
    rw [hinv₀]
    exact hasFDerivAt_exponentialCoordinates hD hcurve g
  refine (hc.comp g.val hinv).congr_of_eventuallyEq ?_
  have hinverse : ∀ᶠ X in 𝓝 g.val, e (inv X) = X := by
    rw [← he₀]
    exact he.eventually_right_inverse
  filter_upwards [hinverse] with X hX
  change unitsExtension F X = F (g * matrixExponentialGL ℂ n (inv X))
  rw [← unitsExtension_val F (g * matrixExponentialGL ℂ n (inv X))]
  exact congrArg (unitsExtension F) hX.symm

variable (n) in
/-- The continuous derivative along each matrix exponential gives the derivative in the
open chart of the complex matrix group. -/
def MatrixGroupDifferentiationStatement : Prop :=
  ∀ (F : G → ℂ) (D : G → Square →L[ℝ] ℂ), Continuous D →
    (∀ (g : G) (X : Square) (t : ℝ),
      HasDerivAt (fun u : ℝ => F (g * matrixExponentialGL ℂ n (u • X)))
        (D (g * matrixExponentialGL ℂ n (t • X)) X) t) →
    ∀ g, HasFDerivAt (unitsExtension F) ((D g).comp (leftMul g).symm.toContinuousLinearMap) g.val

theorem matrixGroupDifferentiation : MatrixGroupDifferentiationStatement n :=
  fun _ _ => hasFDerivAt_unitsExtension

end Langlands.Archimedean.MatrixGroupDifferentiation
