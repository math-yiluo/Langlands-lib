import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenReduction
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingProof

/-! # Affine neighbourhoods of finite sets in an ample proper fibre -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every finite set above a point where the specified line bundle is ample
on the fibre lies in one affine open of the proper family's total space. -/
theorem properFibreAmpleAffineOpen : ProperFibreAmpleAffineOpenStatement.{u} :=
  properFibreAmpleAffineOpen_of_spreading properFibreAmpleSpreading

end Langlands.AlgebraicGeometry.Picard
