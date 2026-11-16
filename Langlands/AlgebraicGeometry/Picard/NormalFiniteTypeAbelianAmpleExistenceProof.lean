import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceReduction
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleProof
import Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionProof

/-! # Ample line bundles on abelian schemes over normal finite-type `ℤ`-domains: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every abelian scheme over the spectrum of an integrally closed finite-type `ℤ`-domain
has an ample line bundle on its total space. -/
theorem normalFiniteTypeAbelianAmpleExistence :
    NormalFiniteTypeAbelianAmpleExistenceStatement.{u} :=
  normalFiniteTypeAbelianAmpleExistence_of_twoAxis_genericAmple
    Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty.{u}
    noetherianAffineAbelianGenericAmple.{u}

end Langlands.AlgebraicGeometry.Picard
