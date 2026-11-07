import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.Reductive.SplitLeviGluingFactorInjectivity
import Langlands.GroupScheme.Reductive.SplitRankOneIsomorphismProof

/-!
# The Isomorphism Theorem for split reductive groups with a common maximal torus

Two connected reductive groups over a field that share a split maximal torus and have the
same roots and coroots are isomorphic by an isomorphism that is the identity on the torus
(Milne, *Algebraic Groups* (2017), Theorem 23.25 and Remark 23.26, for a common torus and
the identity of the character lattice). The proof combines the rank-one case and the gluing
step through `splitCommonTorusIsomorphism_of_rankOne_of_leviGluing`.
-/

universe u

namespace Langlands.GroupScheme

/-- The gluing step holds over every field: the projections of the comparison graph are
isomorphisms over an algebraically closed field, and this descends. -/
theorem splitCommonTorusLeviGluing : SplitCommonTorusLeviGluingStatement.{u} :=
  LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs
    LeviGluing.algClosedGraphProjectionIsomorphisms

/-- **Isomorphism Theorem for a common split maximal torus.** -/
theorem splitCommonTorusIsomorphism : SplitCommonTorusIsomorphismStatement.{u} :=
  splitCommonTorusIsomorphism_of_rankOne_of_leviGluing splitRankOneCommonTorusIsomorphism
    splitCommonTorusLeviGluing

end Langlands.GroupScheme
