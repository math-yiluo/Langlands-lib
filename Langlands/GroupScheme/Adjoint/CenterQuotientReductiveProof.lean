import Langlands.GroupScheme.Adjoint.CenterQuotientCore
import Langlands.GroupScheme.Adjoint.CenterQuotientReduction

/-! # The full-centre quotient of a connected reductive group is connected reductive -/

universe u

namespace Langlands.GroupScheme

/-- **The centre quotient is connected reductive.** Over every field `k`, the target of an
fppf quotient of a connected reductive group by its full scheme-theoretic centre, with affine
target locally of finite type, is connected reductive. -/
theorem centerQuotientReductive : CenterQuotientReductiveStatement.{u} :=
  centerQuotientReductive_of_geometricCore fun _ _ _ _ _ q =>
    CenterQuotient.hasTrivialUnipotentRadical_of_isFppfQuotient_center q

end Langlands.GroupScheme
