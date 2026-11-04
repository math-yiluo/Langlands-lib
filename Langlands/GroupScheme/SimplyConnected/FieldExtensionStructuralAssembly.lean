import Langlands.GroupScheme.SimplyConnected.TensorDescentAscentAssembly
import Langlands.GroupScheme.SimplyConnected.FiniteGaloisExistenceReduction
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Conditional field-extension assembly using proved preservation and splitting -/

universe u

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- Supply proved splitting, semisimplicity and tensor decomposition to the
finite Galois cover-existence reduction. Four structural inputs remain. -/
def simplyConnectedCoverExistence_of_descent_and_splitCover
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u})
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u}) :
    SimplyConnectedCoverExistenceStatement.{u} := by
  apply simplyConnectedCoverExistence_of_finiteGaloisInputs
  refine ⟨torusFiniteGaloisSplitting, hmax, ?_, hcover, hup,
    Langlands.FieldTheory.finiteGaloisTensorDecomposition, hdescent⟩
  intro k L _ _ _ _ _ G hG
  exact isSemisimpleFieldExtension k L G hG

set_option linter.defProp false in
/-- Supply proved semisimplicity and finite Galois torus splitting to the
closure-ascent construction. Seven structural inputs remain. -/
def isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u})
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u}) :
    IsSimplyConnectedAlgebraicClosureAscentStatement.{u} :=
  isSimplyConnectedAlgebraicClosureAscent_of_fullCoverDescent
    hdescent hcover hup isSemisimpleFieldExtension hmax hex hnec hsuff
    torusFiniteGaloisSplitting

/-- Conditional arbitrary field-extension ascent with semisimplicity,
central-isogeny preservation, tensor decomposition and torus splitting supplied
by published proofs. The seven displayed inputs remain hypotheses. -/
theorem isSimplyConnectedFieldExtension_of_descent_and_splitStructure
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u})
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u}) :
    IsSimplyConnectedFieldExtensionStatement.{u} :=
  isSimplyConnectedFieldExtension_of_fullCoverDescent_and_corootCriterion
    hdescent hcover hup isSemisimpleFieldExtension centralIsogenyBaseChange
    hmax hex hnec hsuff torusFiniteGaloisSplitting

end Langlands.GroupScheme
