import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Semisimple

/-! Semisimplicity ascends from a normal subgroup of finite index. -/

namespace Langlands

universe uR uG uV

/-- Let `R` be a field of characteristic zero, `G` a group, `H` a normal
subgroup of finite index in `G`, and `ρ` a representation of `G` on an
`R`-module `V`. If the restriction `ρ.comp H.subtype` of `ρ` to `H` is
semisimple, then `ρ` is semisimple. Semisimplicity is Mathlib's
`Representation.IsSemisimpleRepresentation`: every subrepresentation has a
complementary subrepresentation. The coefficient, group and carrier universes
are independent. No topology, finiteness of `G`, finite dimension of `V`,
irreducibility or finite length is assumed. -/
def FiniteIndexSemisimplicityAscent : Prop :=
  ∀ (R : Type uR) [Field R] [CharZero R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] (ρ : Representation R G V),
    Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) →
      Representation.IsSemisimpleRepresentation ρ

end Langlands
