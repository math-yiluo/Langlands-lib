import Langlands.LocalField.Definitions

/-!
# Topological certificates for a supplied p-adic field realization

`TopologicalData.fieldT2` uses exactly the topology stored in the supplied
realization. It is an explicit certificate, not a global instance.
-/

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

/-- The field is Hausdorff for the topology of this supplied realization. -/
theorem fieldT2 (T : F.TopologicalData) :
    letI := T.topology
    T2Space F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  infer_instance

end TopologicalData

end Langlands.PadicField
