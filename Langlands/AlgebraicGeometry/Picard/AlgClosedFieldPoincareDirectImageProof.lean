import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageAssembly
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionProof

/-! # Higher direct images of the Poincaré bundle over an algebraically closed field -/

universe u

namespace Langlands.AbelianScheme

/-- **Higher direct images of the Poincaré bundle.** Let `A` be an abelian scheme of relative
dimension `g` over an algebraically closed field `K`, with chosen dual `D = dualScheme A hA` and
Poincaré line bundle `P` on `A ×_K D`. Along the projection `p : A ×_K D ⟶ D`, the higher direct
images `Rⁿ p_* P` vanish for `n ≠ g`, and `R^g p_* P` is isomorphic to the pushforward of the
structure sheaf of `Spec K` along the origin of `D`. -/
theorem algClosedFieldPoincareDirectImage : AlgClosedFieldPoincareDirectImageStatement.{u} :=
  PoincareDirectImage.algClosedFieldPoincareDirectImage_of_relativeDimension
    algClosedFieldDualSchemeRelativeDimension

end Langlands.AbelianScheme
