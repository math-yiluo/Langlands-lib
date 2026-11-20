import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.Global.AdelicGL
import Langlands.Global.PositiveRealTorusLog
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Positive split-centre normalization in Arthur–Clozel II.(17.7)–(17.8) -/

noncomputable section

universe uF uE

open MeasureTheory
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.TraceFormula

open Langlands.Global

/-- A continuous unitary character of the positive scalar ideles, parametrized by positive
real units via `PositiveRealIdeles.full`. -/
structure UnitarySplitCenterCharacter where
  toHom : ℝ≥0ˣ →ₜ* ℂˣ
  unitary (a : ℝ≥0ˣ) : ‖(toHom a : ℂ)‖ = 1

/-- The upper character on positive scalar ideles is the pullback by the degree power map. -/
def UnitarySplitCenterCharacter.normPullback (μ : UnitarySplitCenterCharacter) (l : ℕ) :
    UnitarySplitCenterCharacter where
  toHom := μ.toHom.comp
    { toMonoidHom :=
        { toFun := fun a => a ^ l
          map_one' := one_pow l
          map_mul' := fun a b => mul_pow a b l }
      continuous_toFun := continuous_id.pow l }
  unitary a := μ.unitary (a ^ l)

/-- The scalar image of a single positive real in all the actual infinite completions. -/
def adelicPositiveScalar (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    ℝ≥0ˣ →ₜ* AdelicGL F n := (AdelicGL.scalar F n).comp (PositiveRealIdeles.full F)

/-- In the upper determinant coordinate, pull Euclidean measure back by `H_E`.
The parameter of the input measure is the ordinary real logarithm of the scalar. -/
def cyclicUpperCenterMeasure (E : Type uE) [Field E] [NumberField E] (n : ℕ) : Measure ℝ :=
  ((n : ℝ≥0∞) * (Module.finrank ℚ E : ℝ≥0∞)) • volume

/-- In the base coordinate dual to the restriction of the upper rational character,
use the `l`th power of the base determinant. -/
def cyclicBaseCenterMeasure (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) : Measure ℝ :=
  ((n : ℝ≥0∞) * (Module.finrank F E : ℝ≥0∞) * (Module.finrank ℚ F : ℝ≥0∞)) • volume

/-- Central averaging of a full adelic test in §17, written in logarithmic scalar
coordinates. The same expression restricts to the norm-one group. -/
def cyclicCentralAverage (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    (ν : Measure ℝ) (μ : UnitarySplitCenterCharacter) (f : AdelicGL F n → ℂ) :
    AdelicGL F n → ℂ :=
  fun g => ∫ x, let a := PositiveRealTorus.expUnit x
                f (adelicPositiveScalar F n a * g) * (μ.toHom a : ℂ) ∂ν

/-- The actual norm on positive ideles is the degree power map. With the dual-coordinate
Euclidean measures of Chapter II this gives `da' = l da`, written as a pushforward. -/
def CyclicSplitCenterMeasureStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : ℕ), 0 < n →
    (∀ a : ℝ≥0ˣ, AdelicFunctoriality.ideleNorm (K := F) (L := E) (PositiveRealIdeles.full E a) =
      PositiveRealIdeles.full F (a ^ Module.finrank F E)) ∧
    Measure.map (fun x : ℝ => (Module.finrank F E : ℝ) * x) (cyclicUpperCenterMeasure E n) =
      (Module.finrank F E : ℝ≥0∞)⁻¹ • cyclicBaseCenterMeasure F E n

end Langlands.TraceFormula
