import Langlands.AbelianScheme.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-! # Finite freeness of integral Hom groups of abelian varieties -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The actual integral Hom group of two abelian schemes over an algebraically
closed field of characteristic zero is a free, finitely generated ℤ-module.
This is a statement target, not a proof. -/
def HomFiniteFreeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A B : AbelianScheme (Spec (CommRingCat.of k))),
    Module.Free ℤ (A ⟶ B) ∧ Module.Finite ℤ (A ⟶ B)

end Langlands.AbelianScheme
