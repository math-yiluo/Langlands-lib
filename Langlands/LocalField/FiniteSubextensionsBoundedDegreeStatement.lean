import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Set.Finite.Basic

/-!
# Finitely many subextensions of bounded degree of a local field

For a characteristic-zero nonarchimedean local field `F` and a natural number
`d`, the intermediate fields `E` of `AlgebraicClosure F / F` that are
finite-dimensional over `F` with `[E : F] ≤ d` form a finite set.

This module defines that proposition; it does not prove it. The statement is
derived from Serre, *Local Fields* (1979): Chapter I §6 Propositions 17–18,
Chapter II §2 Exercises 1–2 (Krasner's lemma and the local constancy of the
extension defined by a separable polynomial) and Chapter III §5 Theorem 3 and
Corollary 3 (the maximal unramified subextension). See the paired Markdown for
the derivation and the scope.
-/

namespace Langlands.LocalField

universe u

/-- For every characteristic-zero nonarchimedean local field `F` and every natural
number `d`, the set of intermediate fields `E` of `AlgebraicClosure F` over `F` that
are finite-dimensional over `F` with `Module.finrank F E ≤ d` is finite. -/
def FiniteSubextensionsBoundedDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (d : ℕ),
    {E : IntermediateField F (AlgebraicClosure F) |
      FiniteDimensional F E ∧ Module.finrank F E ≤ d}.Finite

end Langlands.LocalField
