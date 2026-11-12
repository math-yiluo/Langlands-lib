import Langlands.GroupScheme.IntegralModel.MaximalCompactStatement
import Langlands.GroupScheme.IntegralModel.IntegralDiagonalRepresentation
import Langlands.GroupScheme.IntegralModel.LeviMaximalCocharacter

/-! # Maximal compactness of the actual integral-point image -/

universe u

namespace Langlands.GroupScheme.IntegralModel

/-- **Levi maximality.** Every supplied model with connected reductive generic group and
special fibre has a cocharacter whose generic centralizer meets the integral points maximally
among compact subgroups, since integral points are open over a local field. -/
theorem leviMaximalCocharacter : LeviMaximalCocharacterStatement.{u} :=
  leviMaximalCocharacterStatement_of_isOpen fun _ _ _ _ _ _ _ M =>
    M.isOpen_integralPoints_localField

/-- **Maximal compactness.** For every supplied model with connected reductive special fibre
of a connected reductive group over a nonarchimedean local field, the integral-point image is
a maximal compact subgroup of the rational points. -/
theorem maximalCompactStatement : MaximalCompactStatement.{u} :=
  maximalCompactStatement_of_integralDiagonalRepresentation integralDiagonalRepresentation
    leviMaximalCocharacter

end Langlands.GroupScheme.IntegralModel
