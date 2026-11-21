import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The strict derivative of the normalized orbit chart -/

noncomputable section

open scoped RightActions

namespace Langlands.BaseChange

universe u v w

variable {F : Type u} {R : Type v} {X : Type w}
  [NontriviallyNormedField F] [NormedRing R] [NormedAlgebra F R]
  [NormedAddCommGroup X] [NormedSpace F X]

/-- With a torus parameter `P x` and transverse parameter `Q x`, the chart
uses the conjugating representative `(1 + Q x)⁻¹` and translates the output
on the right by `a⁻¹`. -/
def normalizedOrbitChart (a : Rˣ) (σ : R →L[F] R) (P Q : X →L[F] R) (x : X) : R :=
  (1 + Q x) * (1 + P x) * a.val * σ (Ring.inverse (1 + Q x)) * (a⁻¹ : Rˣ).val

theorem normalizedOrbitChart_zero (a : Rˣ) (σ : R →L[F] R) (hσ : σ 1 = 1)
    (P Q : X →L[F] R) : normalizedOrbitChart a σ P Q 0 = 1 := by
  simp only [normalizedOrbitChart, map_zero, add_zero, one_mul, Ring.inverse_one, hσ, mul_one]
  exact congrArg Units.val (mul_inv_cancel a)

/-- Near zero the orbit chart has the torus direction plus the transverse
direction, minus the twisted adjoint image of the transverse direction. -/
abbrev OrbitChartDerivativeStatement : Prop :=
  ∀ {F : Type u} {R : Type v} {X : Type w}
    [NontriviallyNormedField F] [NormedRing R] [NormedAlgebra F R]
    [NormedAddCommGroup X] [NormedSpace F X] [HasSummableGeomSeries R]
    (a : Rˣ) (σ : R →L[F] R) (_ : σ 1 = 1) (P Q : X →L[F] R),
    HasStrictFDerivAt (normalizedOrbitChart a σ P Q)
      (Q + P - (ContinuousLinearMap.mulLeftRight F R a.val (a⁻¹ : Rˣ).val).comp (σ.comp Q)) 0

theorem orbitChartDerivative : OrbitChartDerivativeStatement.{u, v, w} := by
  intro F R X _ _ _ _ _ _ a σ hσ P Q
  have hP := P.hasStrictFDerivAt (x := (0 : X)) |>.const_add (c := (1 : R))
  have hQ := Q.hasStrictFDerivAt (x := (0 : X)) |>.const_add (c := (1 : R))
  have hinv : HasStrictFDerivAt (Ring.inverse : R → R) (-ContinuousLinearMap.id F R)
      (1 + Q 0) := by
    rw [map_zero, add_zero]
    convert hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ) using 1
    ext x
    simp [ContinuousLinearMap.mulLeftRight_apply]
  have htwist := σ.hasStrictFDerivAt.comp (0 : X) (hinv.comp (0 : X) hQ)
  have hchart := (((hQ.mul' hP).mul_const' a.val).mul' htwist).mul_const' (a⁻¹ : Rˣ).val
  have ha : a.val * (a⁻¹ : Rˣ).val = 1 := congrArg Units.val (mul_inv_cancel a)
  change HasStrictFDerivAt (normalizedOrbitChart a σ P Q) _ _ at hchart
  convert hchart using 1
  ext x
  simp only [Pi.mul_apply, map_zero, add_zero, Ring.inverse_one, hσ,
    one_mul, mul_one, _root_.smul_apply, _root_.add_apply, _root_.sub_apply, _root_.neg_apply,
    smul_eq_mul, op_smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.mulLeftRight_apply, map_neg, add_mul, mul_neg, neg_mul, mul_assoc, ha]
  abel

end Langlands.BaseChange
