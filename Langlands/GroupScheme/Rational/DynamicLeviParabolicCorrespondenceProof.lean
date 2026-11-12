import Langlands.GroupScheme.Rational.DynamicLeviParabolicTransfer
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.LeviCocharacterRealizationProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Actual parabolics in a represented dynamic Levi: proof -/

universe u

namespace Langlands.GroupScheme

/-- Parabolics of a closed representative of a dynamic centralizer correspond,
by exact extension `j(F) U(χ)` and inverse image along `j`, to the ambient
parabolics contained in the dynamic parabolic, over an arbitrary field. -/
theorem dynamicLeviParabolicCorrespondence :
    DynamicLeviParabolicCorrespondenceStatement.{u} :=
  dynamicLeviParabolicCorrespondenceStatement_of_structural_statements
    parabolicDynamic dynamicCentralizerReductive dynamicLeviCocharacterRealization
    smoothMaximalSplitTorusConjugacy dynamicConnected relativeRootSignInclusions
    relativeRootNegation

end Langlands.GroupScheme
