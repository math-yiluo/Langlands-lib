import Langlands.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly
import Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion
import Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionProof

/-!
# Conditional two-block Godement–Jacquet normalized functional equation

The closed two-block functional-equation statement follows from the conditional
reduction `twoBlockMatrixFunctionalEquationInduction_of_expansion`, applied to the
matched zeta expansion `twoBlockMatchedZetaExpansion` and the two-block analytic
induction `twoBlockMatrixAnalyticInduction`. See the paired Markdown.
-/

namespace Langlands.GodementJacquet

universe uF uV

/-- **Conditional two-block Godement–Jacquet normalized functional equation.**
For two smooth admissible blocks carrying normalized matrix functional-equation
data, the normalized induced representation carries the same data with the
product polynomials, the product epsilon unit and the summed exponent. -/
theorem twoBlockMatrixFunctionalEquationInduction :
    TwoBlockMatrixFunctionalEquationInductionStatement.{uF, uV} :=
  twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockMatchedZetaExpansion
    twoBlockMatrixAnalyticInduction

end Langlands.GodementJacquet
