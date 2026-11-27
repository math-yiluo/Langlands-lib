import Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement
import Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionStatement

/-! # Descent of solutions of strict birational group laws from strictly henselian bases -/

universe u

namespace Langlands.AlgebraicGeometry

/-- If strict birational group laws over every strictly henselian discrete valuation ring in
universe `u` have solutions on their strict domains, then so do strict birational group laws
over every discrete valuation ring in universe `u`. -/
def StrictBirationalGroupLawSolutionDescentStatement : Prop :=
  StrictBirationalGroupLawHenselianSolutionStatement.{u} →
    StrictBirationalGroupLawSolutionStatement.{u}

end Langlands.AlgebraicGeometry
