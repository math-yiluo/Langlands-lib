import Langlands.Global.RankinSelberg.ComplexGodementHalfPlane
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight

/-! # Moving the adjoining radial exponent into the square spectral variable -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams_weight unitaryCompact)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexGodement

local instance adjoiningGLMeasurable (j : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear j ℂ) := borel _

local instance adjoiningGLBorel (j : ℕ) :
    BorelSpace (Langlands.GeneralLinear j ℂ) := ⟨rfl⟩

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

/-- A shift of the radial exponent contributes exactly one extra determinant power. -/
theorem shiftedCharacter_det_apply (d : ComplexCharacterData) (z : ℂ) (g : G) :
    ((shiftedCharacter d z).character (determinant g) : ℂ) =
      (d.character (determinant g) : ℂ) * P g z := by
  let u := determinant g
  have hu : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr u.ne_zero
  have hne : (‖(u : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hP : P g z = (‖(u : ℂ)‖ : ℂ) ^ (2 * z) := by
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hu.le]
    change Complex.exp (z * (Real.log (‖(u : ℂ)‖ ^ 2) : ℂ)) =
      Complex.exp ((Real.log ‖(u : ℂ)‖ : ℂ) * (2 * z))
    rw [Real.log_pow]
    congr 1
    push_cast
    ring
  have hw : (shiftedCharacter d z).weight = d.weight := characterOfParams_weight _ _
  change ((shiftedCharacter d z).character u : ℂ) = (d.character u : ℂ) * P g z
  rw [(shiftedCharacter d z).character_eq, d.character_eq,
    shiftedCharacter_exponent, hw, hP, mul_add, Complex.cpow_add _ _ hne, mul_assoc]

/-- Radial shifts act trivially on the compact determinant character. -/
theorem shiftedCharacter_det_unitary (d : ComplexCharacterData) (z : ℂ) (k : unitaryCompact ℂ n) :
    ((shiftedCharacter d z).character (determinant k.val) : ℂ) =
      (d.character (determinant k.val) : ℂ) := by
  have hdet : complexNormalizedAbs k.val.val.det = 1 := by
    apply Complex.ofReal_injective
    exact Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC_det_unitary k
  rw [shiftedCharacter_det_apply, ArchimedeanLocal.detPower, hdet]
  simp

/-- The determinant twist and the spectral power shift by the sum of their parameters. -/
theorem shiftedCharacter_detWeight (d : ComplexCharacterData) (z t : ℂ) (g : G) :
    complexJacquetDetWeight (shiftedCharacter d z).character.toMonoidHom g t =
      complexJacquetDetWeight d.character.toMonoidHom g (t + z) := by
  change ((shiftedCharacter d z).character (determinant g) : ℂ) * P g t =
    (d.character (determinant g) : ℂ) * P g (t + z)
  rw [shiftedCharacter_det_apply, detPower_complex_add]
  ring

/-- An absolutely convergent square integral with the determinant spectral power
is holomorphic on its open domain of convergence. -/
theorem differentiableOn_matrixDetPowerIntegral (μ : Measure G) (A : G → ℂ) {S : Set ℂ}
    (hS : IsOpen S) (hI : ∀ s ∈ S, Integrable (fun g => A g * P g s) μ) :
    DifferentiableOn ℂ (fun s => ∫ g, A g * P g s ∂μ) S := by
  have hdet : Continuous (fun g : G => complexNormalizedAbs g.val.det) :=
    Units.continuous_val.matrix_det.norm.pow 2
  have hlog : Continuous (fun g : G => Real.log (complexNormalizedAbs g.val.det)) :=
    hdet.log (fun g => (complexNormalizedAbs_det_pos g).ne')
  exact differentiableOn_integral_mul_cexp hlog.measurable hS hI

/-- The shift identity and its restriction to unitary determinants. -/
def ComplexLocalAdjoiningShiftStatement : Prop :=
  (∀ (d : ComplexCharacterData) (z t : ℂ) (g : G),
    complexJacquetDetWeight (shiftedCharacter d z).character.toMonoidHom g t =
      complexJacquetDetWeight d.character.toMonoidHom g (t + z)) ∧
  (∀ (d : ComplexCharacterData) (z : ℂ) (k : unitaryCompact ℂ n),
    ((shiftedCharacter d z).character (determinant k.val) : ℂ) =
      (d.character (determinant k.val) : ℂ))

theorem complexLocalAdjoiningShift : ComplexLocalAdjoiningShiftStatement (n := n) :=
  ⟨shiftedCharacter_detWeight, shiftedCharacter_det_unitary⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
