import Langlands.LocalField.Canonical

/-! # The module topology in a tower of p-adic fields -/

noncomputable section

namespace Langlands.PadicField

universe u v

/-- The canonical topologies on the two fields of a tower are compatible
with the module topology for the upper field over the lower field. -/
def PadicTowerModuleTopologyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    IsModuleTopology F.Carrier E.Carrier

theorem padicTowerModuleTopology : PadicTowerModuleTopologyStatement.{u, v} := by
  intro p _ F E _ _
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.moduleTopology
  let := E.canonicalTopologicalData.moduleTopology
  let : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier E.Carrier
  let b := Module.finBasis F.Carrier E.Carrier
  let e := b.equivFun.symm
  have he : Continuous e :=
    IsModuleTopology.continuous_of_linearMap (e.toLinearMap.restrictScalars (Padic p))
  have he' : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap (e.symm.toLinearMap.restrictScalars (Padic p))
  let ec : (Fin (Module.finrank F.Carrier E.Carrier) → F.Carrier) ≃L[F.Carrier] E.Carrier :=
    ⟨e, he, he'⟩
  exact IsModuleTopology.iso ec

end Langlands.PadicField
