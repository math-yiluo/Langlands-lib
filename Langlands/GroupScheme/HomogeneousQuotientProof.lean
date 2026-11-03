import Langlands.GroupScheme.ProjectiveLineStabilizerQuotient
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Existence of scheme quotients by smooth closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every smooth closed subgroup of a smooth affine group over a field has the
actual homogeneous scheme quotient specified by the published target. -/
theorem smoothSubgroupQuotientExistence :
    SmoothSubgroupQuotientExistenceStatement.{u} := by
  intro k _ G _ _ H i hi hH
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G H i hi
  let Q := ProjectiveOrbit.quotientOfLineStabilizer n i hi hH j ρ hρ
  exact ⟨Q.scheme, Q.projection, Q.separated, Q.locallyOfFiniteType,
    Q.quasiCompact, Q.smooth_projection, Q.surjective_projection,
    Q.quasiCompact_projection, Q.fibers⟩

end Langlands.GroupScheme
