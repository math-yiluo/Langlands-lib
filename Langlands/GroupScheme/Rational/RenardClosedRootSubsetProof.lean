import Langlands.GroupScheme.Rational.RenardClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.ConvexRootSubsetHullProof
import Langlands.GroupScheme.Rational.UnipotentRootSubsetCocharacterProof
import Langlands.GroupScheme.Rational.SymmetricRootSubsetWeylProof
import Langlands.GroupScheme.Rational.StandardParabolicRootTripleProof
import Langlands.GroupScheme.Rational.RootSubsetGroupExistenceProof
import Langlands.GroupScheme.Rational.StandardParabolicRootSubsetGroupProof
import Langlands.GroupScheme.Rational.ConvexRootSubsetGroupIntersectionProof
import Langlands.GroupScheme.Rational.UnipotentRootSubsetGroupIntersectionProof

/-!
# Assembly of the eight published Renard V.4.2 component proofs
-/

namespace Langlands.GroupScheme

universe u

/-- The published eight-part Renard V.4.2 target, assembled from its component proofs. -/
theorem renardClosedRootSubsets : RenardClosedRootSubsetStatements.{u} :=
  ⟨convexRootSubsetHull, unipotentRootSubsetCocharacter, symmetricRootSubsetWeyl,
    standardParabolicRootTriple, rootSubsetGroupExistence, standardParabolicRootSubsetGroup,
    convexRootSubsetGroupIntersection, unipotentRootSubsetGroupIntersection⟩

end Langlands.GroupScheme
