import Langlands.Representation.Families.RenardFamilyAdmissibilityProof
import Langlands.Representation.Families.RenardFamilySpecializationProof
import Langlands.Representation.Families.RenardLocalFreeCoverProof

/-!
# Renard VI.8.1 and VI.8.4: the aggregate statement

A proof of `Statements` by combining the published proofs of its five conjuncts.
-/

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV uE uM

/-- The five VI.8.1 and VI.8.4 statements for general algebraic families. -/
theorem statements : Statements.{uB, uG, uV, uE, uM} :=
  ⟨fixedTensorComparison.{uB, uG, uV, uE}, flatnessCriterion.{uB, uG, uV},
    admissibilityCriterion.{uB, uG, uV}, specializationAdmissibility.{uB, uG, uV},
    localFreeCover.{uB, uM}⟩

end Langlands.Renard.AlgebraicFamily
