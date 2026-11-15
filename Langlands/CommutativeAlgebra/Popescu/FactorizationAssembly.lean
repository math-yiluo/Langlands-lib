import Langlands.CommutativeAlgebra.PopescuFactorizationStatement
import Langlands.CommutativeAlgebra.Popescu.FieldCaseAssembly
import Langlands.CommutativeAlgebra.Popescu.ReductionToFieldAssembly

/-! # Assembly of Popescu's theorem (Stacks 07GC) from its lemmas -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Popescu's theorem in its finite-type factorization form, assuming the lemmas of the Stacks
proof that the Library states separately. -/
theorem popescuFactorization_of (h3 : SingularIdealFactorizationStatement.{u})
    (h5 : NilpotentLiftingStatement.{u}) (h6 : StrictlyStandardDesingularizationStatement.{u})
    (h7 : CharZeroResolutionStatement.{u}) (h8 : CharPResolutionStatement.{u})
    (h9 : LocalizationStandardDescentStatement.{u}) :
    PopescuFactorizationStatement.{u} := by
  intro R S _ _ _ _ _ hreg C _ _ _ f
  have : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  exact reductionToField_of h3 h5 h6 h9 (fieldCase_of_resolutions h3 h7 h8) R S hreg C f

end Langlands.CommutativeAlgebra.Popescu
