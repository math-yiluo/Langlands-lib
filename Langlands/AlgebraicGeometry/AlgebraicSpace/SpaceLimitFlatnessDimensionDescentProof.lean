import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitFlatnessDimensionReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitConnectedFibresDescent

/-! # Conrad's Theorem 3.4(2) for spaces: flatness and fibral pure dimension -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad, printed p.13, Theorem 3.4(2) for finitely presented algebraic spaces: flatness,
and for every `d` nonempty geometrically connected fibres of pure dimension `d`, descend along
cofiltered limits of affine schemes. -/
theorem spaceLimitFlatnessDimensionDescent :
    SpaceLimitFlatnessDimensionDescentStatement.{u} :=
  spaceLimitFlatnessDimensionReduction spaceLimitGeometricallyConnectedFibresDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace
