import Langlands.GroupScheme.SimplyConnected.ClosureAscentReduction
import Langlands.FieldTheory.FiniteGaloisTensorDecompositionProof

/-! # Ascent assembly using the proved finite-Galois tensor decomposition -/

universe u

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- Supply the published tensor decomposition to the conditional closure-ascent
construction. All remaining structural inputs stay explicit. -/
def isSimplyConnectedAlgebraicClosureAscent_of_fullCoverDescent
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u})
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    IsSimplyConnectedAlgebraicClosureAscentStatement.{u} :=
  isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent
    hdescent Langlands.FieldTheory.finiteGaloisTensorDecomposition hcover hup
    hsemi hmax hex hnec hsuff hsplit

/-- Conditional arbitrary field-extension ascent with the finite-Galois tensor
input discharged by its published proof. -/
theorem isSimplyConnectedFieldExtension_of_fullCoverDescent_and_corootCriterion
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u})
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hcentral : CentralIsogenyBaseChangeStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    IsSimplyConnectedFieldExtensionStatement.{u} :=
  isSimplyConnectedFieldExtension_of_algebraicClosureAscent_and_corootCriterion
    hsemi hcentral hmax hex hnec hsuff hsplit
    (isSimplyConnectedAlgebraicClosureAscent_of_fullCoverDescent
      hdescent hcover hup hsemi hmax hex hnec hsuff hsplit)

end Langlands.GroupScheme
