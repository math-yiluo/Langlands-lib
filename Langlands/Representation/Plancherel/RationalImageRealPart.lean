import Langlands.Representation.Plancherel.RationalImageCharacters
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Normalized log modulus on the actual valuation image

These are functionals on the actual image, before identifying its real span
with the real space defined by the split center.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Real additive functionals on the actual integer valuation image. -/
abbrev rationalImageRealFunctionals :=
  Additive (rationalDiscreteValuationImage G) →+ ℝ

/-- The actual complex modulus, as a positive-units-valued character. -/
def rationalImageNorm (χ : rationalImageCharacters G) :
    rationalDiscreteValuationImage G →* ℝ≥0ˣ :=
  (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom).comp χ.toMonoidHom

@[simp]
theorem rationalImageNorm_val (χ : rationalImageCharacters G)
    (a : rationalDiscreteValuationImage G) :
    (((rationalImageNorm G χ a : ℝ≥0) : ℝ)) = ‖(χ a : ℂ)‖ := rfl

/-- The normalized logarithmic modulus with Waldspurger's negative exponent. -/
def rationalImageRealPart (χ : rationalImageCharacters G) :
    rationalImageRealFunctionals G where
  toFun a := normLog (LocalField.residueCardinality F) (rationalImageNorm G χ a.toMul)
  map_zero' := by
    change normLog (LocalField.residueCardinality F) (rationalImageNorm G χ 1) = 0
    rw [map_one, normLog_one]
  map_add' a b := by
    change normLog (LocalField.residueCardinality F)
      (rationalImageNorm G χ (a.toMul * b.toMul)) = _
    rw [map_mul, normLog_mul]

@[simp]
theorem rationalImageRealPart_apply (χ : rationalImageCharacters G)
    (a : rationalDiscreteValuationImage G) :
    rationalImageRealPart G χ (Additive.ofMul a) =
      -Real.log ‖(χ a : ℂ)‖ / Real.log (LocalField.residueCardinality F) := rfl

private theorem residueCardinality_log_ne_zero :
    Real.log (LocalField.residueCardinality F : ℝ) ≠ 0 := by
  apply (Real.log_pos _).ne'
  exact_mod_cast LocalField.residueCardinality_gt_one F

/-- The defining modulus relation on every actual image element. -/
theorem rationalImageRealPart_spec (χ : rationalImageCharacters G)
    (a : rationalDiscreteValuationImage G) :
    (LocalField.residueCardinality F : ℝ) ^
      (-rationalImageRealPart G χ (Additive.ofMul a)) = ‖(χ a : ℂ)‖ := by
  apply rpow_neg_normLog
  exact_mod_cast LocalField.residueCardinality_gt_one F

theorem rationalImageRealPart_mul (χ ψ : rationalImageCharacters G) :
    rationalImageRealPart G (χ * ψ) =
      rationalImageRealPart G χ + rationalImageRealPart G ψ := by
  apply AddMonoidHom.ext
  intro a
  change normLog (LocalField.residueCardinality F) (rationalImageNorm G (χ * ψ) a.toMul) = _
  have h : rationalImageNorm G (χ * ψ) a.toMul =
      rationalImageNorm G χ a.toMul * rationalImageNorm G ψ a.toMul := by
    apply Units.ext
    change ‖((χ a.toMul : ℂ) * (ψ a.toMul : ℂ))‖₊ = _
    exact nnnorm_mul _ _
  rw [h, normLog_mul]
  rfl

/-- Zero logarithmic modulus means precisely norm one. -/
theorem rationalImageRealPart_eq_zero_iff (χ : rationalImageCharacters G) :
    rationalImageRealPart G χ = 0 ↔
      χ ∈ unitaryCharacters (rationalDiscreteValuationImage G) := by
  have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  constructor
  · intro h a
    have he := DFunLike.congr_fun h (Additive.ofMul a)
    change normLog (LocalField.residueCardinality F) (rationalImageNorm G χ a) = 0 at he
    have hn := (normLog_eq_zero_iff hq _).mp he
    exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hn
  · intro h
    apply AddMonoidHom.ext
    intro a
    apply (normLog_eq_zero_iff hq _).mpr
    apply Units.ext
    apply NNReal.eq
    exact h a.toMul

/-- The positive character belonging to a real functional, on the actual
discrete image. Continuity follows from discreteness. -/
def rationalImagePositiveCharacter (phi : rationalImageRealFunctionals G) :
    rationalImageCharacters G where
  toFun a := Units.mk0
    (Real.exp (-phi (Additive.ofMul a) * Real.log (LocalField.residueCardinality F)) : ℂ)
    (by exact_mod_cast Real.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    change (Real.exp (-phi (Additive.ofMul (a * b)) *
      Real.log (LocalField.residueCardinality F)) : ℂ) = _
    rw [show phi (Additive.ofMul (a * b)) =
      phi (Additive.ofMul a) + phi (Additive.ofMul b) from map_add phi _ _]
    simp only [neg_add, add_mul, Real.exp_add, Complex.ofReal_mul, Units.val_mul,
      Units.val_mk0]
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem rationalImagePositiveCharacter_val (phi : rationalImageRealFunctionals G)
    (a : rationalDiscreteValuationImage G) :
    (rationalImagePositiveCharacter G phi a : ℂ) =
      (Real.exp (-phi (Additive.ofMul a) * Real.log (LocalField.residueCardinality F)) : ℂ) :=
  rfl

@[simp]
theorem rationalImagePositiveCharacter_norm (phi : rationalImageRealFunctionals G)
    (a : rationalDiscreteValuationImage G) :
    ‖(rationalImagePositiveCharacter G phi a : ℂ)‖ =
      Real.exp (-phi (Additive.ofMul a) * Real.log (LocalField.residueCardinality F)) := by
  rw [rationalImagePositiveCharacter_val, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Positive characters form a section of the normalized log modulus. -/
@[simp]
theorem rationalImageRealPart_positive (phi : rationalImageRealFunctionals G) :
    rationalImageRealPart G (rationalImagePositiveCharacter G phi) = phi := by
  apply AddMonoidHom.ext
  intro a
  change -Real.log ‖(rationalImagePositiveCharacter G phi a.toMul : ℂ)‖ /
    Real.log (LocalField.residueCardinality F) = phi a
  rw [rationalImagePositiveCharacter_norm, Real.log_exp, neg_mul, neg_neg]
  exact mul_div_cancel_right₀ _ (residueCardinality_log_ne_zero (F := F))

/-- Reconstructing the positive character gives exactly the original modulus. -/
theorem rationalImagePositiveCharacter_realPart_val (χ : rationalImageCharacters G)
    (a : rationalDiscreteValuationImage G) :
    (rationalImagePositiveCharacter G (rationalImageRealPart G χ) a : ℂ) =
      (‖(χ a : ℂ)‖ : ℂ) := by
  rw [rationalImagePositiveCharacter_val, rationalImageRealPart_apply]
  have hc : -(-Real.log ‖(χ a : ℂ)‖ / Real.log (LocalField.residueCardinality F)) *
      Real.log (LocalField.residueCardinality F) = Real.log ‖(χ a : ℂ)‖ := by
    rw [neg_div, neg_neg, div_mul_cancel₀ _ (residueCardinality_log_ne_zero (F := F))]
  rw [hc, Real.exp_log (norm_pos_iff.mpr (Units.ne_zero _))]

/-- Dividing by the positive character produces an actual norm-one character. -/
def rationalImageUnitaryPart (χ : rationalImageCharacters G) :
    unitaryCharacters (rationalDiscreteValuationImage G) :=
  ⟨χ / rationalImagePositiveCharacter G (rationalImageRealPart G χ), fun a => by
    change ‖(χ a : ℂ) /
      (rationalImagePositiveCharacter G (rationalImageRealPart G χ) a : ℂ)‖ = 1
    rw [rationalImagePositiveCharacter_realPart_val, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (Units.ne_zero _))]⟩

/-- The original character is the product of its unitary and positive parts. -/
theorem rationalImageUnitaryPart_mul_positive (χ : rationalImageCharacters G) :
    (rationalImageUnitaryPart G χ).val *
      rationalImagePositiveCharacter G (rationalImageRealPart G χ) = χ :=
  div_mul_cancel _ _

/-- Unitary multiplication leaves the logarithmic modulus unchanged. -/
theorem rationalImageRealPart_unitary_mul
    (θ : unitaryCharacters (rationalDiscreteValuationImage G))
    (phi : rationalImageRealFunctionals G) :
    rationalImageRealPart G (θ.val * rationalImagePositiveCharacter G phi) = phi := by
  rw [rationalImageRealPart_mul,
    (rationalImageRealPart_eq_zero_iff G θ.val).mpr θ.property,
    rationalImageRealPart_positive, zero_add]

end Langlands.Plancherel
