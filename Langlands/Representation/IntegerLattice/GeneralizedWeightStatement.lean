import Langlands.Representation.IntegerLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Simultaneous generalized weights of commuting invertible tuples -/

set_option autoImplicit false

namespace Langlands

universe u

/-- Renard C.III's common blocks, stated basis-free: the intersections over all
coordinates of the maximal generalized eigenspaces of the actual tuple entries,
labelled by tuples of nonzero complex numbers, have finite nonzero support, are
independent, span the space, and are each mapped bijectively onto themselves by
the action of every point of the integer lattice. -/
def CommutingTupleGeneralizedWeightDecompositionStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : IntegerLattice.CommutingInvertibleTuple d V),
    {c : Fin d → ℂˣ |
        (⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)) ≠ ⊥}.Finite ∧
      iSupIndep (fun c : Fin d → ℂˣ =>
        ⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)) ∧
      (⨆ c : Fin d → ℂˣ,
        ⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)) = ⊤ ∧
      ∀ (c : Fin d → ℂˣ) (n : IntegerLattice.Lattice d),
        Set.BijOn (IntegerLattice.tupleRepresentationEquiv d V A n)
          (⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ) : Submodule ℂ V)
          (⨅ i, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ) : Submodule ℂ V)

end Langlands
