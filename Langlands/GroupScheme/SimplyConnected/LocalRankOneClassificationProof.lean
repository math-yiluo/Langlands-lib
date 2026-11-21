import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationIndexReduction
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexProof
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneProof
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankProof
import Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianProof
import Langlands.GroupScheme.SimplyConnected.TypeCRankOneQuaternionicProof
import Langlands.GroupScheme.SimplyConnected.TypeDRankOneSpinIndexReduction
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof

/-!
# The local rank-one classification (Prasad–Raghunathan 1985, §2)

An absolutely almost-simple, simply connected group of split rank one over a
nonarchimedean local field is `SL₂(D)`, a special unitary group of a hermitian
form of Witt index one in three or four variables, or a quaternionic symplectic
or spin group of Witt index one. The proof applies the published index reduction
`localRankOneClassification_of_indexStatements` to the seven published input
theorems; it has no hypothesis.
-/

universe u

namespace Langlands.GroupScheme

/-- The classification of absolutely almost-simple simply connected groups of
split rank one over nonarchimedean local fields, in every characteristic of the
field and of its residue field and at every universe. -/
theorem localRankOneClassification : LocalRankOneClassificationStatement.{u} :=
  localRankOneClassification_of_indexStatements titsIndexExistence localRankOneTitsIndex
    innerTypeANormOne CentralSimpleUnits.matrixNormOneSplitRank outerTypeARankOneHermitian
    typeCRankOneQuaternionic
    (typeDRankOneSpin_of_classicalTypeDSpinPresentation classicalTypeDSpinPresentation)

end Langlands.GroupScheme
