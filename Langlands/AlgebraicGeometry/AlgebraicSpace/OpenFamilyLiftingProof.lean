import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting

/-! # Lifting covering open scheme charts across arbitrary thickenings -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The actual lifted family retains its pullbacks, thickenings and local coverage. -/
theorem openFamilyLifting : OpenFamilyLiftingStatement.{u} :=
  OpenSubfunctorLifting.openFamilyLifting

end Langlands.AlgebraicGeometry.AlgebraicSpace
