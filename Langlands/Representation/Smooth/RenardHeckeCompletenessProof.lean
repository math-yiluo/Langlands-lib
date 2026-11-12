import Langlands.Representation.Smooth.RenardHeckeCompletenessReduction
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof

/-! # Renard III.1.11: completeness of irreducible smooth representations -/

universe u v

namespace Langlands.Renard.Smooth

/-- Every nonzero actual Hecke element is detected by an irreducible smooth
representation, with carrier in an independently prescribed universe. -/
theorem heckeCompleteness : HeckeCompletenessStatement.{u, v} :=
  heckeCompleteness_of_equivalence Hecke.heckeNondegenerateModuleEquivalence

end Langlands.Renard.Smooth
