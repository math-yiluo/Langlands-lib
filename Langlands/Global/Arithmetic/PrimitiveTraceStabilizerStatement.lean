import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Trace.Basic

/-!
# Primitive coefficients with exact trace-functional stabilizer

An internal algebraic prerequisite for the additive-character route to auxiliary
local characters. These proposition definitions do not assert character existence.
-/

noncomputable section

universe u v

namespace Langlands.Global

/-- The trace functional with coefficient `a` has precisely the subgroup fixing
`L` as its stabilizer under precomposition by actual `F`-automorphisms of `M`. -/
def HasExactTraceStabilizer
    {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M]
    (L : IntermediateField F M) (a : L) : Prop :=
  ∀ σ : M ≃ₐ[F] M,
    (∀ x : M,
      Algebra.trace F M ((a : M) * σ x) =
      Algebra.trace F M ((a : M) * x)) ↔
    σ ∈ L.fixingSubgroup

/-- Every intermediate field of a finite separable extension has a nonzero
primitive coefficient whose trace functional has exact pointwise stabilizer.
The two ambient carrier universes are independent. -/
def PrimitiveTraceStabilizerStatement : Prop :=
  ∀ (F : Type u) (M : Type v) [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] [Algebra.IsSeparable F M]
    (L : IntermediateField F M),
    ∃ a : L, a ≠ 0 ∧
      IntermediateField.adjoin F ({a} : Set L) = ⊤ ∧
      HasExactTraceStabilizer L a

end Langlands.Global
