import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndexStatement
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex

/-! # Proof of the finite-index restriction of rational characters to a split component

This proves `CharacterRestrictionFiniteIndexStatement` from the published theorem
`IsSplitComponent.finiteIndex_range_characterRestrict`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Renard V.2.6, finite index.** Over every field `k`, for a split component `i : A ⟶ G` of a
connected reductive group `G`, the range of the restriction `X^*(G)_k → X^*(A)` has finite index
in `X^*(A)`. -/
theorem characterRestrictionFiniteIndexStatement : CharacterRestrictionFiniteIndexStatement.{u} :=
  fun _ _ _ hG _ _ hi => hi.finiteIndex_range_characterRestrict hG

end Langlands.GroupScheme
