import Langlands.Geometry.Building.FullValidity.AssignmentReplacement
import Langlands.Geometry.Building.FullValidity.UnramifiedDescent

/-! # Group-valid data from unramified descent -/

universe u

namespace Langlands.Geometry.Building

/-- Replace a datum satisfying the one-group axioms of corrected Definition
4.1.26 by a group-valid datum whose building and models come from unramified
descent. The comparison of their reduced buildings is equivariant along
the identity on rational points. -/
def UnramifiedDescentOfGroupAxiomsStatement : Prop :=
  ∀ (p : KPBuildingAssignment.DatumIndex.{u}) (D : KPBuildingDatum p.G),
    D.SatisfiesGroupAxioms →
      ∃ D' : KPBuildingDatum p.G,
        D'.SatisfiesGroupAxioms ∧ D'.SatisfiesUnramifiedDescent ∧
          Nonempty (KPBuildingDatum.BuildingEquivalence D D')

end Langlands.Geometry.Building
