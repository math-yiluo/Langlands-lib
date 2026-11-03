module

public import Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Local finite dimensionality of coalgebras

This module states the fundamental theorem of coalgebras: each element of a
coalgebra over a field belongs to a finite-dimensional subcoalgebra.
The paired Markdown explains the general-coalgebra source correspondence.
-/

public section

universe u v

namespace Langlands.Subcoalgebra

/-- Every element of an arbitrary field coalgebra belongs to a subcoalgebra
whose actual carrier is finite dimensional over that field. -/
@[expose] def LocalFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (C : Type v) [AddCommGroup C] [Module k C]
    [Coalgebra k C] (c : C),
    ∃ D : Langlands.Subcoalgebra k C, c ∈ D ∧ FiniteDimensional k D

end Langlands.Subcoalgebra
