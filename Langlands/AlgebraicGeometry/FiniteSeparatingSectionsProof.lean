import Langlands.AlgebraicGeometry.FiniteSeparating.Core
import Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionProof

/-!
# Finitely many sections separate points and tangent vectors

The Noetherian finite-family construction in `FiniteSeparating.Core`, applied to the
published local closed-immersion criterion, proves `FiniteSeparatingSectionsStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry

/-- A separating line bundle on a proper scheme over an algebraically closed field has
a finite family without common zeros whose span separates rational points and tangents. -/
theorem finiteSeparatingSections : FiniteSeparatingSectionsStatement.{u} :=
  finiteSeparatingSections_of properRationalImmersion_localClosedImmersion.{u}

end Langlands.AlgebraicGeometry
