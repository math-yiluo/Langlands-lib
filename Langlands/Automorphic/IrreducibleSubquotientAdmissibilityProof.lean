import Langlands.Automorphic.IrreducibleSubquotientAdmissibilityReduction
import Langlands.Automorphic.GeneratedFormAdmissibilityProof

/-! # Joint admissibility of irreducible operator subquotients -/

universe u

namespace Langlands.Automorphic

/-- Borel–Jacquet §4.6 for `GL_n` over a number field. -/
theorem irreducibleSubquotientAdmissibility :
    IrreducibleSubquotientAdmissibilityStatement.{u} :=
  irreducibleSubquotientAdmissibility_of_generatedFormAdmissibility
    generatedFormAdmissibility

end Langlands.Automorphic
