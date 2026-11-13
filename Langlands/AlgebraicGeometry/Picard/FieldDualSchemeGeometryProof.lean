import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryReduction
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSmoothProof

/-! # Smoothness, properness and geometric connectedness of the chosen dual over a field

The published reduction `FieldDualSchemeGeometryStatement.of_smooth` derives the full geometry
statement from smoothness; the published theorem `fieldDualSchemeSmooth` supplies smoothness.
-/

universe u

namespace Langlands.AbelianScheme

/-- The chosen universal geometric Picard-zero parameter scheme over every field is smooth,
proper and geometrically connected. -/
theorem fieldDualSchemeGeometry : FieldDualSchemeGeometryStatement.{u} :=
  FieldDualSchemeGeometryStatement.of_smooth fieldDualSchemeSmooth

end Langlands.AbelianScheme
