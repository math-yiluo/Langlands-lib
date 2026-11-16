import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements

/-!
# Renard V.4.2 on closed sets of relative roots, without Borel-Tits 3.22 b)

The conjunction `ClosedRootSubsetStatements` also contains
`ClosedRootSubsetGroupIntersectionStatement`, the form of Borel-Tits 3.22 b) for closed
subsets whose intersection is convex. That assertion has a paper counterexample in split
`SO₈` (see the Markdown file). Renard V.4.2 does not state it: its intersection result (i)
assumes that both subsets are convex, which is `ConvexRootSubsetGroupIntersectionStatement`.
`RenardClosedRootSubsetStatements` is the conjunction of the other eight statements.
-/

universe u

namespace Langlands.GroupScheme

/-- The statements of Renard V.4.2 on closed subsets of relative roots: the components of
`ClosedRootSubsetStatements` other than `ClosedRootSubsetGroupIntersectionStatement`
(Borel-Tits 3.22 b) for closed subsets with convex intersection). -/
def RenardClosedRootSubsetStatements : Prop :=
  ConvexRootSubsetHullStatement.{u} ∧ UnipotentRootSubsetCocharacterStatement.{u} ∧
    SymmetricRootSubsetWeylStatement.{u} ∧ StandardParabolicRootTripleStatement.{u} ∧
    RootSubsetGroupExistenceStatement.{u} ∧ StandardParabolicRootSubsetGroupStatement.{u} ∧
    ConvexRootSubsetGroupIntersectionStatement.{u} ∧
    UnipotentRootSubsetGroupIntersectionStatement.{u}

end Langlands.GroupScheme
