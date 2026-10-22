import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support

/-! Algebraic evaluation of a reciprocal, restricted to its denominator's support. -/

namespace Langlands.LocalFactor.RegularEvaluation

universe u v w

variable {X : Type u} {Y : Type v} {K : Type w}

/-- The existing Mathlib support subtype, with no analytic structure on the input. -/
abbrev Point [Zero K] (denominator : X → K) :=
  ↥(Function.support denominator)

/-- Evaluate the reciprocal as a unit only where its denominator is nonzero. -/
def value [Field K] (denominator : X → K) (x : Point denominator) : Kˣ :=
  (Units.mk0 (denominator x.val) x.property)⁻¹

@[simp]
theorem coe_value [Field K] (denominator : X → K) (x : Point denominator) :
    (value denominator x : K) = (denominator x.val)⁻¹ := rfl

/-- Substitution sends a regular input of the composite to a regular input of
the original denominator. It need not be an equivalence. -/
def mapInput [Zero K] (denominator : X → K) (input : Y → X)
    (y : Point (denominator ∘ input)) : Point denominator :=
  ⟨input y.val, y.property⟩

@[simp]
theorem mapInput_val [Zero K] (denominator : X → K) (input : Y → X)
    (y : Point (denominator ∘ input)) :
    (mapInput denominator input y).val = input y.val := rfl

@[simp]
theorem value_mapInput [Field K] (denominator : X → K) (input : Y → X)
    (y : Point (denominator ∘ input)) :
    value denominator (mapInput denominator input y) =
      value (denominator ∘ input) y := rfl

end Langlands.LocalFactor.RegularEvaluation
