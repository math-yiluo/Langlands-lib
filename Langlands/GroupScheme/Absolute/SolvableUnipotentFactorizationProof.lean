import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationOfQuotient
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Rational unipotent-times-maximal-torus factorization -/

universe u

namespace Langlands.GroupScheme

/-- Every rational point of a smooth connected affine solvable group over an
algebraically closed field factors through a smooth connected normal unipotent
closed subgroup followed by any caller-supplied maximal torus. -/
theorem solvableUnipotentFactorization : SolvableUnipotentFactorizationStatement.{u} :=
  solvableUnipotentFactorization_of_solvableTorusQuotient solvableTorusQuotient

end Langlands.GroupScheme
