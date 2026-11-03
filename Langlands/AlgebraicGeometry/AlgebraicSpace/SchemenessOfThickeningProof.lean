import Langlands.AlgebraicGeometry.AlgebraicSpace.ThickeningAssembly
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentProof

/-! # Schemeness under arbitrary thickenings

Stacks Project Lemma 76.9.5 (Tag 05ZR), proved by lifting affine open charts,
finite-surjective affine descent, and gluing over the original base.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An arbitrary thickening of a scheme-represented algebraic space is scheme-represented. -/
theorem schemenessOfThickening : SchemenessOfThickeningStatement.{u} :=
  ThickeningAssembly.schemeness_of_finite_descent finiteSurjectiveAffineDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace
