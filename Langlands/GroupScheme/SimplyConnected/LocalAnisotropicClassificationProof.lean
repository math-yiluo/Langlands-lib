import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicClassificationReduction
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankProof
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneProof
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAInnerProof
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAReduction
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramProof

/-!
# Proof: anisotropic simply connected groups over local fields are `SL_1(D)`

This module proves `LocalAnisotropicSimplyConnectedClassificationStatement`
(Bruhat–Tits 1967, Proposition 6, over nonarchimedean local fields). It applies the
published reduction `localAnisotropicSimplyConnectedClassification_of_statements` to
the published proofs of its four inputs.
-/

universe u

namespace Langlands.GroupScheme

/-- **Bruhat–Tits (1967), Proposition 6, over local fields.** Every affine, anisotropic,
simply connected, absolutely almost-simple group over a nonarchimedean local field, of any
characteristic, is isomorphic as a group scheme to the reduced-norm-one group
`CentralSimpleUnits.normOne K D` of a finite-dimensional central division algebra `D`. -/
theorem localAnisotropicSimplyConnectedClassification :
    LocalAnisotropicSimplyConnectedClassificationStatement.{u} :=
  localAnisotropicSimplyConnectedClassification_of_statements titsIndexExistence
    ⟨localAnisotropicTypeA_of_affineDiagram localAnisotropicAffineDiagram,
      localAnisotropicTypeAInner⟩
    innerTypeANormOne CentralSimpleUnits.matrixNormOneSplitRank

end Langlands.GroupScheme
