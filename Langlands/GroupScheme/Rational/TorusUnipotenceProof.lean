import Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGlue

/-! # Unipotence from the absence of zero Lie weights for split torus actions -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- CGP, Proposition 2.3.11 (general observation in its proof): a smooth connected affine group
with a split torus action having no zero Lie weight is unipotent. -/
theorem torusActionUnipotence : TorusActionUnipotenceStatement.{u} := by
  intro k _ H hSm hAff hConn S hS b
  let := hAff
  let := hSm
  let := hConn
  exact TorusUnipotence.isUnipotent_of_actionWeightSpace_zero_eq_bot hS b

end Langlands.GroupScheme.RelativeRoot
