import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction

/-! # Proof: the Isomorphism Theorem in semisimple rank at most one, common torus -/

universe u

namespace Langlands.GroupScheme

/-- **Isomorphism Theorem in semisimple rank at most one, common torus** (Milne, *Algebraic
Groups* (2017), Proposition 23.14, isomorphism case, combined with Proposition 23.5). -/
theorem splitRankOneCommonTorusIsomorphism :
    SplitRankOneCommonTorusIsomorphismStatement.{u} :=
  splitRankOneCommonTorusIsomorphism_of_rootCell splitRankOneRootCell

end Langlands.GroupScheme
