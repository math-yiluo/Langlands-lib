import Langlands.GroupScheme.Rational.TorusVectorLinearizationStatement
import Langlands.GroupScheme.Rational.TorusVectorLinearization.Assembly
import Langlands.GroupScheme.Rational.TorusLinearization.Linearizing

/-! # Linearization of torus actions on vector groups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

open TorusLinearization

/-- Every action of a torus on a vector group over a field is linear in suitable coordinates. -/
theorem torusVectorActionLinearization : TorusVectorActionLinearizationStatement.{u} :=
  torusVectorActionLinearization_of_linearizing fun _ _ _ _ _ _ p _ _ _ _ a =>
    a.exists_linearizing p

end Langlands.GroupScheme.RelativeRoot
