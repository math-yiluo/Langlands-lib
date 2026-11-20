import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Global.RankinSelberg.ComplexMatrixSchwartzConvergence
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # A right half-plane for complex Schwartz Godement tests -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexMatrixSchwartz (complexMatrixSchwartzConvergence)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance schwartzGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance schwartzGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Square (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

private def trailingColumns (m : ℕ) : Rect m →ₗ[ℝ] Square m where
  toFun X := X.submatrix id Fin.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem trailingRows_right_mul {m : ℕ} (g : Langlands.GeneralLinear (m + 1) ℂ) :
    trailingRows g.val * g⁻¹.val = trailingRows 1 := by
  calc
    _ = (g.val * g⁻¹.val).submatrix Fin.succ id :=
      (Matrix.submatrix_mul g.val g⁻¹.val Fin.succ id id Function.bijective_id).symm
    _ = _ := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl

/-- The restriction of a rectangular Schwartz test along `X ↦ X · trailingRows(g)` is
Schwartz on the square matrix space. -/
def pullbackRectangularTest {m : ℕ} (g : Langlands.GeneralLinear (m + 1) ℂ) :
    𝓢(Rect m, ℂ) →L[ℂ] 𝓢(Square m, ℂ) := by
  let A := (mulRightLinearMap (Fin m) ℝ (trailingRows g.val)).toContinuousLinearMap
  let B := ((trailingColumns m).comp (mulRightLinearMap (Fin m) ℝ g⁻¹.val)).toContinuousLinearMap
  have hBA (X : Square m) : B (A X) = X := by
    ext i j
    change ((X * trailingRows g.val) * g⁻¹.val) i j.succ = X i j
    rw [Matrix.mul_assoc, trailingRows_right_mul]
    simp [trailingRows, Matrix.mul_apply, Matrix.one_apply, mul_ite]
  refine SchwartzMap.compCLM ℂ A.hasTemperateGrowth ⟨1, ‖B‖, fun X => ?_⟩
  calc
    ‖X‖ = ‖B (A X)‖ := by rw [hBA]
    _ ≤ ‖B‖ * ‖A X‖ := B.le_opNorm _
    _ ≤ ‖B‖ * (1 + ‖A X‖) ^ (1 : ℕ) := by
      rw [pow_one]
      gcongr
      exact le_add_of_nonneg_left zero_le_one

@[simp]
theorem pullbackRectangularTest_apply {m : ℕ} (g : Langlands.GeneralLinear (m + 1) ℂ)
    (Φ : 𝓢(Rect m, ℂ)) (X : Square m) :
    pullbackRectangularTest g Φ X = Φ (X * trailingRows g.val) := rfl

theorem norm_characterWeight (d : ComplexCharacterData) (s : ℂ) (z : ℂˣ) :
    ‖characterWeight d s z‖ = complexNormalizedAbs (z : ℂ) ^ (d.exponent + s).re := by
  have hr : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hp : ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hradial : ‖(z : ℂ)‖ ^ (2 * d.exponent).re =
      (‖(z : ℂ)‖ ^ (2 : ℕ)) ^ d.exponent.re := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    simp
  change ‖(d.character z : ℂ) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s‖ = _
  rw [d.character_eq, norm_mul, norm_mul, Complex.norm_zpow, hp, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, hradial,
    Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hr (2 : ℕ)),
    ← Real.rpow_add (pow_pos hr (2 : ℕ)), Complex.add_re]
  rfl

/-- For a continuous smaller-group input bounded by a power of the matrix height at inverse
arguments, the Godement integrand against a rectangular Schwartz test is integrable in a
right half-plane of the added character's exponent. -/
theorem integrable_godementSectionIntegrand_of_height_bound {m M : ℕ} {C : ℝ}
    (d : ComplexCharacterData) (Φ : 𝓢(Rect m, ℂ)) {f : Langlands.GeneralLinear m ℂ → ℂ}
    (hf : Continuous f) (hbound : ∀ h, ‖f h⁻¹‖ ≤ C * complexMatrixHeight h ^ M)
    (hₛ : (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re)
    (g : Langlands.GeneralLinear (m + 1) ℂ) :
    Integrable (godementSectionIntegrand d Φ f g) (complexGeneralLinearHaar m) := by
  let s := d.exponent + ((m : ℂ) + 1) / 2
  let Ψ := pullbackRectangularTest g Φ
  have hj := complexMatrixSchwartzConvergence m M Ψ s hₛ
  have hpair : Continuous (fun h : Langlands.GeneralLinear m ℂ => (g, h)) :=
    continuous_const.prodMk continuous_id
  have hcont := (continuous_godementSectionIntegrand (m := m) d Φ.continuous hf).comp hpair
  change Continuous (godementSectionIntegrand d Φ f g) at hcont
  refine (hj.norm.const_mul C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with h
  let a := complexNormalizedAbs h.val.det
  have ha : 0 < a := pow_pos (norm_pos_iff.mpr h.det_ne_zero) _
  calc
    ‖godementSectionIntegrand d Φ f g h‖ =
        ‖Ψ h.val‖ * ‖f h⁻¹‖ * a ^ s.re := by
      rw [godementSectionIntegrand, norm_mul, norm_mul, norm_characterWeight,
        pullbackRectangularTest_apply]
      rfl
    _ ≤ ‖Ψ h.val‖ * (C * complexMatrixHeight h ^ M) * a ^ s.re := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hbound h) (norm_nonneg _)) (Real.rpow_nonneg ha.le _)
    _ = C * ‖(complexMatrixHeight h ^ M : ℝ) * Ψ h.val * (a : ℂ) ^ s‖ := by
      have hH : 0 ≤ complexMatrixHeight h := by unfold complexMatrixHeight; positivity
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hH _), Complex.norm_cpow_eq_rpow_re_of_pos ha]
      ring

/-- The Schwartz Godement integral of a continuous height-bounded input converges in the
specified right half-plane of the added exponent. -/
def ComplexGodementSchwartzStatement : Prop :=
  ∀ (m M : ℕ) (C : ℝ) (d : ComplexCharacterData) (Φ : 𝓢(Rect m, ℂ))
    (f : Langlands.GeneralLinear m ℂ → ℂ), Continuous f →
    (∀ h, ‖f h⁻¹‖ ≤ C * complexMatrixHeight h ^ M) →
    (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re →
    ∀ g, Integrable (godementSectionIntegrand d Φ f g) (complexGeneralLinearHaar m)

theorem complexGodementSchwartz : ComplexGodementSchwartzStatement := by
  intro m M C d Φ f hf hbound hₛ g
  exact integrable_godementSectionIntegrand_of_height_bound d Φ hf hbound hₛ g

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
