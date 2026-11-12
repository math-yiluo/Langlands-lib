import Langlands.AbelianScheme.AlgebraicallyClosedProjectivityStatement
import Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleProof
import Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityProof

/-! # Projectivity over an algebraically closed field

The separating line bundle on the group scheme gives an actual closed immersion
into polynomial-Proj projective space by the very-ampleness criterion.
-/

universe u

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field admits a closed immersion into a finite
polynomial-Proj projective space over the field. -/
theorem algebraicallyClosedProjectivity :
    AlgebraicallyClosedProjectivityStatement.{u} := by
  intro K _ _ G _ hsm hpr hgc
  obtain ⟨L, hL⟩ := algebraicallyClosedSeparatingLineBundle K G hsm hpr hgc
  exact Langlands.AlgebraicGeometry.separatingLineBundleHProjectivity
    K G.X.left G.X.hom L hpr hL

end Langlands.GroupScheme
