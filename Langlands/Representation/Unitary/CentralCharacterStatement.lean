import Langlands.Representation.Unitary.Basic
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Mathlib.RepresentationTheory.Irreducible

/-!
# Unitary central characters from invariant positive forms

This internal proposition records the central-character existence consequence
of irreducibility, admissibility, and algebraic unitarizability.
-/

namespace Langlands

universe uG uV

/-- An irreducible admissible unitarizable complex representation has an actual
smooth unitary central character, with no chosen form or carrier norm as input. -/
def UnitarizableCentralCharacterStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    IsAdmissible ρ → ρ.IsIrreducible → IsUnitarizable ρ →
      Nonempty (UnitaryCentralCharacter ρ)

end Langlands
