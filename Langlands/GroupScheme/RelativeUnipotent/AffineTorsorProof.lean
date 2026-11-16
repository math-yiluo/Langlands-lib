import Langlands.GroupScheme.RelativeUnipotent.AffineTorsorStatement
import Langlands.GroupScheme.RelativeUnipotent.VectorBundleSeriesCocycle

/-! # Affine torsors under groups with finite vector-bundle series -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual fpqc torsor under a smooth affine group supplied with a finite
vector-bundle normal series has a section over an arbitrary affine base. -/
theorem relativeUnipotentAffineTorsor : RelativeUnipotentAffineTorsorStatement.{u} := by
  intro S _ U _ _ hseries X _ hflat hsurj hqc hiso
  exact RelativeUnipotent.AffineCocycle.exists_section_of_cocyclesVanish_at_base
    hseries.cocyclesVanish X hflat hsurj hqc hiso

end Langlands.GroupScheme
