import Langlands.Sheaf.Renard.EquivariantModuleEquivalence
import Langlands.Sheaf.Renard.SheafComparisonIsIsoProof
import Langlands.Sheaf.Renard.ModuleProjectorComparisonProof

/-!
# Renard III.3.1–III.3.2: the equivariant sheaf and compatible test-module equivalences

The published II.2.5 comparison isomorphisms discharge the two hypotheses of
`EquivariantModuleEquivalence.statements_of_comparisons`.
-/

namespace Langlands.Sheaf.Renard.EquivariantModuleStatements

universe uG

/-- Renard III.3.1 with the exact published functors, and its restriction to the
whole-module smooth subcategories of III.3.2. -/
theorem statements : Statements.{uG} :=
  EquivariantModuleEquivalence.statements_of_comparisons
    CompactSectionEquivalence.sheafComparisonIsIso
    ModuleProjectorComparison.moduleComparisonIsIso

end Langlands.Sheaf.Renard.EquivariantModuleStatements
