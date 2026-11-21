import Langlands.Global.RankinSelberg.RealRankZeroHaar
import Langlands.LocalFactor.Archimedean.RealTateZeta
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Mathlib.MeasureTheory.Integral.Pi

/-! # Additive Tate weights on the full real diagonal -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Global.RankinSelbergGlobal.RealRankZero
open Langlands.LocalFactor.RealTate (integrand)
open Langlands.Archimedean.RealJacquetFrobenius (charFun)

local instance realTateUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance realTateUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩

local instance invAbsVolumeSigmaFinite : SigmaFinite invAbsVolume := by
  unfold invAbsVolume
  infer_instance

private def diagonalDensity {n : ℕ} (x : Fin n → ℝ) : ℝ≥0 := ∏ i, invAbs (x i)

private theorem measurable_diagonalDensity {n : ℕ} : Measurable (diagonalDensity (n := n)) :=
  Finset.measurable_prod _ fun i _ => measurable_invAbs.comp (measurable_pi_apply i)

private theorem pi_invAbsVolume (n : ℕ) :
    Measure.pi (fun _ : Fin n => invAbsVolume) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => (diagonalDensity x : ℝ≥0∞)) := by
  induction n with
  | zero =>
    have h : (fun x : Fin 0 → ℝ => (diagonalDensity x : ℝ≥0∞)) = 1 := by
      funext x
      simp [diagonalDensity]
    rw [h, withDensity_one, volume_pi]
    exact Measure.pi_eq fun s _ => by rw [Measure.pi_pi]; simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hleft := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => invAbsVolume) 0).map_eq
    have hright := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).map_eq
    apply e.measurableEmbedding.map_injective
    rw [show Measure.map e (Measure.pi (fun _ : Fin (n + 1) => invAbsVolume)) =
        invAbsVolume.prod (Measure.pi (fun _ : Fin n => invAbsVolume)) from hleft]
    rw [Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv,
      show Measure.map e (volume : Measure (Fin (n + 1) → ℝ)) =
        (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from hright,
      ih, invAbsVolume, prod_withDensity
        measurable_invAbs.coe_nnreal_ennreal measurable_diagonalDensity.coe_nnreal_ennreal]
    congr 1
    funext p
    simp only [diagonalDensity, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero, ENNReal.coe_mul]

private theorem map_realMultiplicativeDiagonal (n : ℕ) :
    (Measure.pi (fun _ : Fin n => unitsHaar)).map (fun d i => (d i : ℝ)) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => (diagonalDensity x : ℝ≥0∞)) := by
  let : SigmaFinite (unitsHaar.map Units.val) := by rw [map_val_unitsHaar]; infer_instance
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => unitsHaar) (f := fun _ => Units.val)
    (fun _ => measurableEmbedding_val.measurable.aemeasurable)]
  simp only [map_val_unitsHaar, pi_invAbsVolume]

/-- Inverting a nonzero real argument negates the exponent and leaves the parity unchanged. -/
theorem realCharFun_inv (e : Fin 2) (u : ℂ) {x : ℝ} (hx : x ≠ 0) :
    charFun e u x⁻¹ = charFun e (-u) x := by
  have hsign : x⁻¹ / |x⁻¹| = x / |x| := by
    rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg (inv_lt_zero.mpr h), abs_of_neg h, div_neg, div_neg,
        div_self (inv_ne_zero hx), div_self hx]
    · rw [abs_of_pos (inv_pos.mpr h), abs_of_pos h, div_self (inv_ne_zero hx), div_self hx]
  rw [charFun, charFun, hsign, abs_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (abs_nonneg x), Complex.cpow_neg]

private theorem scalarTateWeight (e : Fin 2) (u : ℂ) (x : ℝ) :
    ((invAbs x : ℝ) : ℂ) * charFun e u x = integrand (fun _ => 1) e u x := by
  by_cases hx : x = 0
  · simp [hx, invAbs, integrand]
  · simp only [invAbs, NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs, Complex.ofReal_inv,
      charFun, integrand, ite_eq_right hx, one_mul]
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)), Complex.cpow_one,
      div_eq_mul_inv]
    ring

/-- The multiplicative diagonal with Tate characters becomes the product of the additive
Tate densities, both for integrability and for integration. -/
def RealDiagonalTateIntegrationStatement : Prop :=
  ∀ (n : ℕ) (e : Fin n → Fin 2) (u : Fin n → ℂ) (F : (Fin n → ℝ) → ℂ), Measurable F →
    let δ := Measure.pi (fun _ : Fin n => unitsHaar)
    let P (d : Fin n → ℝˣ) := F (fun i => (d i : ℝ)) * ∏ i, charFun (e i) (u i) (d i : ℝ)
    let A (x : Fin n → ℝ) := F x * ∏ i, integrand (fun _ => 1) (e i) (u i) (x i)
    (Integrable P δ ↔ Integrable A) ∧ (∫ d, P d ∂δ) = ∫ x, A x

theorem realDiagonalTateIntegration : RealDiagonalTateIntegrationStatement := by
  intro n e u F hF δ P A
  let v (d : Fin n → ℝˣ) (i : Fin n) : ℝ := d i
  let Q (x : Fin n → ℝ) := F x * ∏ i, charFun (e i) (u i) (x i)
  have hv : Measurable v := Measurable.of_eval fun i =>
    measurableEmbedding_val.measurable.comp (measurable_pi_apply i)
  have hQ : Measurable Q := hF.mul (Finset.measurable_prod _ fun i _ =>
    (show Measurable (charFun (e i) (u i)) by unfold charFun; fun_prop).comp (measurable_pi_apply i))
  have hmap : δ.map v = volume.withDensity (fun x => (diagonalDensity x : ℝ≥0∞)) :=
    map_realMultiplicativeDiagonal n
  have hA : (fun x => diagonalDensity x • Q x) = A := by
    funext x
    rw [NNReal.smul_def, Complex.real_smul, diagonalDensity, NNReal.coe_prod, Complex.ofReal_prod]
    change (∏ i, ((invAbs (x i) : ℝ) : ℂ)) * (F x * ∏ i, charFun (e i) (u i) (x i)) = A x
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    simp_rw [scalarTateWeight]
    rfl
  change (Integrable (Q ∘ v) δ ↔ Integrable A) ∧ (∫ d, Q (v d) ∂δ) = ∫ x, A x
  rw [← integrable_map_measure hQ.aestronglyMeasurable hv.aemeasurable,
    ← integral_map hv.aemeasurable hQ.aestronglyMeasurable, hmap,
    integrable_withDensity_iff_integrable_smul measurable_diagonalDensity,
    integral_withDensity_eq_integral_smul measurable_diagonalDensity, hA]
  exact ⟨Iff.rfl, rfl⟩

end Langlands.GodementJacquet
