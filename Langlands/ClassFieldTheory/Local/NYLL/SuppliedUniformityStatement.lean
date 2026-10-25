import Langlands.ClassFieldTheory.Local.NYLL.SuppliedUniformity

/-!
# Compatibility target for the supplied additive right uniformity

This proposition refers to the published `suppliedUniformSpace` construction
for arbitrary supplied local-field data. This module states the target only.
-/

namespace Langlands.LocalClassField.NYLL

universe u

/-- The named right uniformity retains the supplied topology and makes the
additive group uniform, for every supplied p-adic field realization. -/
def SuppliedUniformityCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (suppliedUniformSpace T).toTopologicalSpace = T.topology ∧
      (letI := suppliedUniformSpace T
       IsUniformAddGroup F.Carrier)

end Langlands.LocalClassField.NYLL
