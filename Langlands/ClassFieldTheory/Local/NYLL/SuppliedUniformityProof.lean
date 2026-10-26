import Langlands.ClassFieldTheory.Local.NYLL.SuppliedUniformityStatement

/-!
# Compatibility of the supplied additive right uniformity
-/

namespace Langlands.LocalClassField.NYLL

universe u

/-- The named supplied right uniformity retains the topology and makes addition uniform. -/
theorem suppliedUniformityCompatibility :
    SuppliedUniformityCompatibilityStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  constructor
  · rfl
  · exact isUniformAddGroup_of_addCommGroup (G := F.Carrier)

end Langlands.LocalClassField.NYLL
