import Langlands.Global.AdelicSpreadSmoothOpenOfLangWeilProof
import Langlands.AlgebraicGeometry.UniformLangWeilProof

/-! # Conrad's Theorem 4.5 on actual adelic points -/

universe u

namespace Langlands.Global

/-- A smooth surjective map with geometrically connected fibres between separated
generic fibres over a global field induces an open map on actual adelic points,
for arbitrary finite-type spreads of the source and target. -/
theorem adelicSpreadSmoothOpen : AdelicSpreadSmoothOpenStatement.{u} :=
  adelicSpreadSmoothOpenOfLangWeil Langlands.AlgebraicGeometry.uniformLangWeil

end Langlands.Global
