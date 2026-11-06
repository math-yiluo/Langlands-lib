import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityComposition
import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof
import Langlands.GroupScheme.Rational.MaximalTorusParameterUnirationalProof

/-! # Density of conjugators onto ground-field maximal tori -/

universe u

namespace Langlands.GroupScheme

/-- Over every infinite field, the geometric points conjugating a fixed maximal torus
onto a closed ground-field torus are Zariski-dense. -/
theorem rationalMaximalTorusConjugateDensity :
    RationalMaximalTorusConjugateDensityStatement.{u} :=
  rationalMaximalTorusConjugateDensity_of_parameter_statements
    maximalTorusParameterExistence maximalTorusParameterUnirational

end Langlands.GroupScheme
