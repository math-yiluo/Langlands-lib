import Langlands.GroupScheme.Rational.CharacterRestrictionReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof

/-! # Restriction of rational characters to a split component -/

universe u

namespace Langlands.GroupScheme

/-- For every field `k`, every connected reductive group `G` over `Spec k` and every split
component `i : A.toGrp ⟶ G`, restriction of rational characters along `i` is injective and its
range has finite index. -/
theorem characterRestriction : CharacterRestrictionStatement.{u} :=
  characterRestriction_of_torusSurjectivity reductiveCentralTorusSurjectivity.{u}

end Langlands.GroupScheme
