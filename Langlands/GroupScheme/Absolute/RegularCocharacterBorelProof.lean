import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.RegularCocharacterBorel
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Borel subgroups from regular cocharacters of split maximal tori

The proof of `RegularCocharacterBorelStatement`: the assembly
`regularCocharacterBorelStatement_of_relativeRootNegation` applied to the Library proof
`relativeRootNegation`. -/

universe u

namespace Langlands.GroupScheme

/-- **Borel subgroups from regular cocharacters** (Milne, *Algebraic Groups*, 21.29 and 21.32).
Over a field, for a connected reductive `G` with a split maximal torus `j : T ⟶ G`: every closed
subgroup representing the dynamic parabolic `P(ν ≫ j)` of a regular cocharacter `ν` is a Borel
subgroup; for regular `ν` and `ν'`, `P(ν ≫ j) = P(ν' ≫ j)` exactly when `ν` and `ν'` are positive
on the same roots; and every Borel subgroup through which `j` factors represents some
`P(ν ≫ j)` with `ν` regular. -/
theorem regularCocharacterBorel : RegularCocharacterBorelStatement.{u} :=
  regularCocharacterBorelStatement_of_relativeRootNegation relativeRootNegation

end Langlands.GroupScheme
