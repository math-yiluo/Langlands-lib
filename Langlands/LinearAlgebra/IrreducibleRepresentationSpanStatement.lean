import Mathlib.RepresentationTheory.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Full endomorphism span for an irreducible representation -/

universe u v w

namespace Langlands.LinearAlgebra

/-- Over an algebraically closed field, the operators of a finite-dimensional
irreducible monoid representation span all linear endomorphisms. -/
def IrreducibleRepresentationSpanStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (H : Type v) [Monoid H]
    (V : Type w) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K H V),
    Representation.IsIrreducible ρ →
      Submodule.span K (Set.range ρ) = ⊤

end Langlands.LinearAlgebra
