import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Semisimple

/-! Finite-dimensional semisimplicity descends to a normal subgroup. -/

namespace Langlands

universe uR uG uV

/-- A semisimple finite-dimensional representation of a group over any field
remains semisimple after restriction to a normal subgroup. Semisimplicity means
that the lattice of subrepresentations is complemented. The coefficient, group,
and carrier universes are independent; the zero-dimensional case is included.
There is no finite-index or characteristic assumption. This is a proposition
statement, not a proof of the restriction theorem. -/
def FiniteDimensionalNormalRestrictionSemisimplicity : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    (H : Subgroup G) [H.Normal] (ρ : Representation R G V),
    Representation.IsSemisimpleRepresentation ρ →
      Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)

end Langlands
