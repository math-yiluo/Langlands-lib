import Langlands.GroupScheme.Adjoint.CenterQuotientDescent
import Langlands.GroupScheme.Adjoint.SecondCenterReductive
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof

/-! # The full-centre quotient of a connected reductive group has trivial centre -/

universe u

namespace Langlands.GroupScheme

/-- **The centre quotient has trivial centre.** Over every field `k`, the target of an fppf
quotient of a connected reductive group by its full scheme-theoretic centre, with affine target
locally of finite type, has trivial scheme-theoretic centre on every test scheme. -/
theorem centerQuotientCenterTrivial : CenterQuotientCenterTrivialStatement.{u} :=
  CenterQuotientCenter.centerQuotientCenterTrivial_of_secondCenterTrivial fun k _ G hG =>
    SecondCenter.secondCenterTrivial_of_centralDerivedProduct reductiveCentralDerivedProduct.{u}
      k G hG

end Langlands.GroupScheme
