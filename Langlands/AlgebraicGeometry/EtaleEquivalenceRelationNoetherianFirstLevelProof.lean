import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianFirstLevelStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleTailNextSystem

/-! # A Noetherian first level of a separated étale equivalence relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry

/-- Every separated étale equivalence relation on an affine scheme has a
cartesian first level with affine Noetherian objects and affine arrows. -/
theorem etaleEquivalenceRelationNoetherianFirstLevel :
    EtaleEquivalenceRelationNoetherianFirstLevelStatement.{u} := by
  intro E hU hj
  let : IsAffine E.U := hU
  let : IsClosedImmersion (prod.lift E.t E.s) := hj
  let : IsAffine E.R := E.isAffine_relation
  let : IsSeparated E.s := inferInstance
  obtain ⟨M⟩ := E.nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems
    E.tupleLengthBound (fun p hp M =>
      E.nonempty_finiteTypeCartesianSystem_tupleTailNext
        E.tupleLengthBound p le_rfl hp M)
  exact ⟨M.relation, M.comparison.objMap, M.comparison.relMap,
    M.comparison.isCartesian, M.object_isAffine, inferInstance, M.arrows_isAffine⟩

end Langlands.AlgebraicGeometry
