import Langlands.GroupScheme.Torus.MaximalModuliLocalQuasiAffine
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeQuotientProof

/-! # Quasi-affineness of supplied universal maximal-torus moduli -/

universe u

namespace Langlands.GroupScheme

/-- Every supplied universal maximal-torus family in a reductive group has
relatively quasi-affine parameter scheme. -/
theorem maximalTorusModuliQuasiAffine :
    MaximalTorusModuliQuasiAffineStatement.{u} :=
  maximalTorusModuliQuasiAffine_of_quotient relativeMultiplicativeTypeQuotient

end Langlands.GroupScheme
