import Langlands.CommutativeAlgebra.PopescuFactorizationStatement
import Langlands.CommutativeAlgebra.Popescu.FactorizationAssembly
import Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationProof
import Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationProof
import Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentProof
import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionProof
import Langlands.CommutativeAlgebra.Popescu.CharPResolutionProof

/-! # Popescu's theorem (Stacks 07GC), finite-type factorization form -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Popescu's theorem: for a regular map `R → S` of Noetherian rings, every `R`-algebra map from a
finite-type `R`-algebra to `S` factors through a smooth `R`-algebra. -/
theorem popescuFactorization : PopescuFactorizationStatement.{u} :=
  popescuFactorization_of singularIdealFactorization NilpotentLifting.nilpotentLifting
    Desing.strictlyStandardDesingularization charZeroResolution charPResolution
    localizationStandardDescent

end Langlands.CommutativeAlgebra.Popescu
