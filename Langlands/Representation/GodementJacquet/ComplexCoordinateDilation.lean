import Langlands.Representation.GodementJacquet.ComplexMatrixHaar
import Langlands.Representation.GodementJacquet.ComplexCoordinateFourier

/-! # Changes of variables by coordinatewise complex multiplication -/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {ι : Type*} [Fintype ι]
local notation "Z" => ι → ℂ

/-- The additive Jacobian of coordinatewise multiplication by `x`. -/
def complexCoordinateJacobian (x : Z) : ℝ≥0 :=
  ∏ i, complexAbsHom (x i)

theorem complexCoordinateJacobian_ne_zero {x : Z} (hx : ∀ i, x i ≠ 0) :
    complexCoordinateJacobian x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero 2 (nnnorm_ne_zero_iff.mpr (hx i))

theorem ae_complexCoordinate_ne_zero (a : ℂˣ) :
    ∀ᵐ x ∂complexCoordinateMeasure ι a, ∀ i, x i ≠ 0 := by
  let μ := (complexSelfDualMeasure a).measure
  let : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  apply eventually_all.2
  intro i
  have h := Measure.tendsto_eval_ae_ae (μ := fun _ : ι => μ) (i := i)
  exact h.eventually (Measure.ae_ne μ (0 : ℂ))

private def complexCoordinateDilation (x : Z) (hx : ∀ i, x i ≠ 0) : Z ≃ᵐ Z :=
  MeasurableEquiv.piCongrRight fun i =>
    let e := (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (x i) (hx i))).restrictScalars ℝ
    e.toHomeomorph.toMeasurableEquiv

omit [Fintype ι] in
private theorem complexCoordinateDilation_apply (x : Z) (hx : ∀ i, x i ≠ 0) (z : Z) :
    complexCoordinateDilation x hx z = x * z := by
  ext i
  change z i * x i = x i * z i
  exact mul_comm _ _

private theorem map_complexCoordinateDilation (a : ℂˣ) (x : Z) (hx : ∀ i, x i ≠ 0) :
    (complexCoordinateMeasure ι a).map (complexCoordinateDilation x hx) =
      (complexCoordinateJacobian x)⁻¹ • complexCoordinateMeasure ι a := by
  let μ := (complexSelfDualMeasure a).measure
  let : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  classical
  have hd : (Matrix.diagonal x).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx i
  have h := productMeasure_map_diagonal μ complexAbsHom
    (fun z hz => map_complex_mul_addHaar μ hz) hd
  have he : (Matrix.toLin' (Matrix.diagonal x) : Z → Z) = complexCoordinateDilation x hx := by
    funext z
    ext i
    rw [complexCoordinateDilation_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    rfl
  rw [he, Matrix.det_diagonal, map_prod] at h
  exact h

/-- The pushforward under a nonzero diagonal multiplication scales by the inverse Jacobian. -/
theorem map_complexCoordinateMul (a : ℂˣ) (x : Z) (hx : ∀ i, x i ≠ 0) :
    (complexCoordinateMeasure ι a).map (fun z => x * z) =
      (complexCoordinateJacobian x)⁻¹ • complexCoordinateMeasure ι a := by
  rw [← funext (complexCoordinateDilation_apply x hx), map_complexCoordinateDilation]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinatewise complex change of variables in a Bochner integral. -/
theorem integral_complexCoordinateDilation (a : ℂˣ) (x : Z) (hx : ∀ i, x i ≠ 0)
    (F : Z → E) :
    (∫ z, F (x * z) ∂complexCoordinateMeasure ι a) =
      ((complexCoordinateJacobian x)⁻¹ : ℝ) • ∫ z, F z ∂complexCoordinateMeasure ι a := by
  rw [← funext (complexCoordinateDilation_apply x hx)]
  rw [← integral_map_equiv (complexCoordinateDilation x hx) F,
    map_complexCoordinateDilation, integral_smul_nnreal_measure]
  rfl

omit [NormedSpace ℝ E] in
/-- Absolute integrability is preserved by a coordinatewise nonzero complex dilation. -/
theorem integrable_complexCoordinateDilation (a : ℂˣ) (x : Z) (hx : ∀ i, x i ≠ 0)
    {F : Z → E} (hF : Integrable F (complexCoordinateMeasure ι a)) :
    Integrable (fun z => F (x * z)) (complexCoordinateMeasure ι a) := by
  rw [← funext (complexCoordinateDilation_apply x hx)]
  have h := integrable_map_equiv (μ := complexCoordinateMeasure ι a)
    (complexCoordinateDilation x hx) F
  rw [map_complexCoordinateDilation] at h
  exact h.mp (hF.smul_measure ENNReal.coe_ne_top)

end Langlands.GodementJacquet
