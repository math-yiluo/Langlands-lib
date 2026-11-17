import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionProof
import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeReduction
import Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeProof
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceProof
import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceProof

/-!
# Scheme representability of the Picard sheaf over finite-type `ℤ`-algebras: proof

The fppf Picard class sheaf of every abelian scheme over a finite-type `ℤ`-algebra is
represented by a scheme. The proof composes two published reductions with three published
unconditional theorems:

* `finiteTypeAbelianPicardSheafAlgebraicSpace`: the Picard sheaf is an algebraic space;
* `normalFiniteTypeAbelianAmpleExistence`: over a normal finite-type `ℤ`-domain the total
  space of an abelian scheme has an ample line bundle;
* `ampleNormalFiniteTypeAbelianPicardSheafAFScheme`: over a normal finite-type `ℤ`-domain,
  with an ample line bundle, the Picard sheaf is represented by an AF scheme.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For every commutative ring `R` of finite type over `ℤ` and every abelian scheme `A` over
`Spec R`, the fppf Picard class sheaf of `A` is represented by a scheme over `Spec R`. -/
theorem finiteTypeAbelianPicardSheafScheme :
    FiniteTypeAbelianPicardSheafSchemeStatement.{u} :=
  finiteTypeAbelianPicardSheafScheme_of_algebraicSpace_of_normal
    finiteTypeAbelianPicardSheafAlgebraicSpace.{u}
    (normalFiniteTypeAbelianPicardSheafAFScheme_of_ample
      normalFiniteTypeAbelianAmpleExistence.{u}
      ampleNormalFiniteTypeAbelianPicardSheafAFScheme.{u})

end Langlands.AlgebraicGeometry.Picard
