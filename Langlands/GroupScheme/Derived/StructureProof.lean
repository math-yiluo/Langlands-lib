import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.Derived.ConnectednessProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SmoothnessProof

/-!
# Proof of `Langlands.GroupScheme.DerivedSubgroupStructureStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `DerivedSubgroupStructureStatement`. -/
theorem derivedSubgroupStructure : DerivedSubgroupStructureStatement.{u} :=
  ⟨derivedSubgroupRepresentability, derivedSubgroupFieldBaseChange,
    derivedSubgroupSmoothness, derivedSubgroupConnectedness⟩

end Langlands.GroupScheme
