import Langlands.GroupScheme.Torus.UnitsProductGeometricReduction
import Langlands.GroupScheme.Torus.UnitsProductAffineReduction
import Langlands.Algebra.RosenlichtTensorUnits

/-! # Splitting invertible functions on a product of irreducible varieties -/

universe u

namespace Langlands.GroupScheme

/-- Every invertible function on the product splits into functions on the factors. -/
theorem unitsProductDecomposition : UnitsProductDecompositionStatement.{u} :=
  UnitsProduct.geometric_reduction
    (UnitsProduct.affine_splitting_of_domain_tensor_units
      Langlands.Algebra.rosenlichtTensorUnits.{u,u,u})

end Langlands.GroupScheme
