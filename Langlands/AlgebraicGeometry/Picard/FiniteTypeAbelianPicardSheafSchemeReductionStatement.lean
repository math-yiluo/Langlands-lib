import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement
import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeStatement

/-! # Scheme representability of the Picard sheaf from the algebraic-space and normal cases -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- If the Picard sheaf of every abelian scheme over a finite-type `ℤ`-algebra is an
algebraic space, and over every integrally closed finite-type `ℤ`-domain it is represented
by a scheme whose finite sets of points lie in affine opens, then over every finite-type
`ℤ`-algebra it is represented by a scheme. -/
def FiniteTypeAbelianPicardSheafSchemeReductionStatement : Prop :=
  FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} →
    NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} →
      FiniteTypeAbelianPicardSheafSchemeStatement.{u}

end Langlands.AlgebraicGeometry.Picard
