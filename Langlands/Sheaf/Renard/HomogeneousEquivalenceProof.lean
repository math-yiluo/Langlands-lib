import Langlands.Sheaf.Renard.HomogeneousCounit
import Langlands.Sheaf.Renard.HomogeneousCompactSectionProof
import Langlands.Sheaf.Renard.EquivariantModuleProof

/-!
# Proof: Renard III.3.2, induction and original-stalk restriction are an equivalence

The conditional assembly `HomogeneousEquivalence.statement_of` is applied to the
published III.3.1 smooth equivalence and the published compact alpha/beta comparison.
-/

namespace Langlands.Sheaf.Renard.HomogeneousEquivalence

/-- Renard III.3.2: induction of smooth representations of a closed subgroup and
restriction to the identity-coset stalk form an equivalence of categories with the
published functors. -/
theorem homogeneousEquivalence : Statement :=
  statement_of EquivariantModuleStatements.statements.2
    HomogeneousCompactSectionProof.compactAlphaBeta

end Langlands.Sheaf.Renard.HomogeneousEquivalence
