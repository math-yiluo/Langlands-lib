import Langlands.Representation.Families.RenardFamilyInductionBaseChangeProof
import Langlands.Representation.Families.RenardFamilyJacquetFiniteTypeProof

/-!
# Renard VI.8.2 and VI.8.3: the conjunction

A proof of `ParabolicStatements` from the proofs of its two conjuncts.
-/

namespace Langlands.Renard.AlgebraicFamily

universe u uB uC uE uV

/-- The VI.8.2 and VI.8.3 Propositions together. -/
theorem parabolicStatements : ParabolicStatements.{u, uB, uC, uE, uV} :=
  ⟨inductionBaseChange.{u, uB, uC, uE}, jacquetFiniteType.{u, uB, uV}⟩

end Langlands.Renard.AlgebraicFamily
