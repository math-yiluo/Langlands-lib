import Langlands.LocalField.Topology

/-!
# The additive right uniformity of supplied local-field data

This explicit adapter retains the topology in `PadicField.TopologicalData`.
It reuses the local construction in `PadicField.TopologicalData.fieldT2`.
-/

namespace Langlands.LocalClassField.NYLL

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

/-- The additive right uniformity for the topology of the supplied realization. -/
@[instance_reducible]
def suppliedUniformSpace (TF : F.TopologicalData) : UniformSpace F.Carrier := by
  letI := TF.topology
  letI := TF.valuativeRel
  letI := TF.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  haveI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  infer_instance

end Langlands.LocalClassField.NYLL
