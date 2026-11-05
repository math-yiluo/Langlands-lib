import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Defs

/-! # The norm criterion for fields of dimension at most one -/

universe u

namespace Langlands.FieldTheory

/-- The finite-separable norm criterion for a field to have dimension at most one.
This is the field-theoretic dimension, rather than the Krull dimension of a ring. -/
def HasDimensionLEOne (K : Type u) [Field K] : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (L : Type u) [Field L] [Algebra E L]
    [FiniteDimensional E L] [IsGalois E L],
    Function.Surjective (Units.map (Algebra.norm E : L →* E))

end Langlands.FieldTheory
