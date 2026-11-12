import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackStatement
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackAssembly
import Langlands.AbelianScheme.FieldCubePullbackProof

/-! # Multiplication pullback of symmetric line bundles over arbitrary fields -/

universe u

namespace Langlands.GroupScheme

/-- Pullback of a symmetric line bundle by positive multiplication by `n`
is isomorphic to its actual `n * n`-th tensor power over any field. -/
theorem fieldSymmetricMultiplicationPullback :
    FieldSymmetricMultiplicationPullbackStatement.{u} :=
  fieldSymmetricMultiplicationPullbackOfCube fieldCubePullback.{u}

end Langlands.GroupScheme
