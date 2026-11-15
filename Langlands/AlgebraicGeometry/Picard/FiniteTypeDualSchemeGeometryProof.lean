import Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.DualSchemeGeometryAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingProof

/-! # Geometry of the chosen dual over a finite-type `ℤ`-algebra -/

universe u

namespace Langlands.AbelianScheme

/-- Let `R` be a commutative ring of finite type over `ℤ` and `A` an abelian scheme over
`Spec R`. For every proof `hA` that an actual universal Picard-zero family exists, the chosen
parameter scheme is smooth, proper and geometrically connected over `Spec R`. -/
theorem finiteTypeDualSchemeGeometry : FiniteTypeDualSchemeGeometryStatement.{u} :=
  finiteTypeDualSchemeGeometryReduction relativeDualSchemeValuativeExistence.{u}
    picardZeroArtinianLifting.{u}

end Langlands.AbelianScheme
