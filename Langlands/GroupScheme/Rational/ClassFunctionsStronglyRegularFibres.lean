import Langlands.GroupScheme.Rational.ClassFunctionsAlgClosedStronglyRegularFibres
import Langlands.GroupScheme.Absolute.BorelPointContainmentProof
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationProof
import Langlands.GroupScheme.Dynamic.UnipotentConjugation

/-! # Strongly regular fibres of the canonical class-function quotient -/

universe u

namespace Langlands.GroupScheme.ClassFunctions

/-- **Strongly regular fibres are geometric conjugacy classes.** For a simply connected
quasi-split group, two points with the same image under the canonical class-function quotient
`ClassFunctions.rho G`, one of whose all-test centralizers lies in a closed torus, become
conjugate over a field extension. -/
theorem stronglyRegularFibres : StronglyRegularFibresStatement.{u} :=
  stronglyRegularFibres_of_inputs borelPointContainment torusSeparation
    Dynamic.exists_unipotent_conj_eq_mul

end Langlands.GroupScheme.ClassFunctions
