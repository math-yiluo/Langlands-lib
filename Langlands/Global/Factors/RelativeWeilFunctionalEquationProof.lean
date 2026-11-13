import Langlands.Global.Factors.RelativeWeilFunctionalEquationAssembly
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof

/-!
# The global functional equation for twisted relative Weil pairs

Proof of `RelativeWeilTwistFunctionalEquationStatement` (Tate (1979), Theorem 3.5.3, for
twisted pairs of representations of relative Weil groups; Henniart (2000), §2.3).
-/

universe u uV uE

namespace Langlands.Global.FunctionalEquationComparison

/-- **Global functional equation for twisted relative Weil pairs** (Tate (1979), Theorem
3.5.3; Henniart (2000), §2.3). -/
theorem relativeWeilTwistFunctionalEquation :
    RelativeWeilTwistFunctionalEquationStatement.{u, uV, uE} :=
  relativeWeilTwistFunctionalEquation_of_localTransferReciprocity
    ClassField.Global.RelativeWeilGroup.localTransferReciprocity.{u}

end Langlands.Global.FunctionalEquationComparison
