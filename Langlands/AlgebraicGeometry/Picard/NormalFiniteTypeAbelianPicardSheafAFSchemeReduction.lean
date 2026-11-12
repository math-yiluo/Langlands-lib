import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceStatement
import Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement
import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeStatement

/-! # The normal-base Picard statement from ampleness and the projective case -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Existence of an ample line bundle over a normal finite-type `ℤ`-domain, together with the
projective case, gives the normal-base Picard statement. -/
theorem normalFiniteTypeAbelianPicardSheafAFScheme_of_ample
    (ample : NormalFiniteTypeAbelianAmpleExistenceStatement.{u})
    (projective : AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}) :
    NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} :=
  fun R _ _ _ _ A => projective R A (ample R A)

end Langlands.AlgebraicGeometry.Picard
