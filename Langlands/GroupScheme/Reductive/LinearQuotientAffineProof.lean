import Langlands.GroupScheme.Reductive.IndependentGeometricReductivityProof
import Langlands.GroupScheme.Reductive.LinearQuotientAffineOfGeometricReductivity

/-! # Affineness of linear homogeneous quotients by connected reductive subgroups -/

universe u

namespace Langlands.GroupScheme

/-- Every supplied linear homogeneous quotient in the published statement is affine. -/
theorem reductiveLinearQuotientAffine : ReductiveLinearQuotientAffineStatement.{u} :=
  reductiveLinearQuotientAffine_of_geometricReductivity
    IndependentHaboush.reductiveGeometricReductivity

end Langlands.GroupScheme
