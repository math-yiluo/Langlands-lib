import Langlands.Algebra.IntegerOriginalSubmoduleNoetherianStatements

/-!
# Noetherian criteria for the original nonunital action

Proofs of the published internal statement aggregate, using the original
nonunital action and the actual integer-unitized module.
-/

set_option autoImplicit false

namespace Langlands.Algebra.IntegerOriginalSubmoduleNoetherian

universe uA uM

/-- Transfer ordinary module Noetherianity through the actual subgroup
order isomorphism for the original action. -/
theorem accCriterion : ACCStatement.{uA, uM} := by
  intro A M _ _ _
  let unitizedModule := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  let e := NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M)
  rw [isNoetherian_iff]
  constructor
  · intro h
    exact e.toOrderEmbedding.dual.wellFoundedLT
  · intro h
    exact e.symm.toOrderEmbedding.dual.wellFoundedLT

/-- The maximal-element criterion in the original subgroup poset. -/
theorem maximalCriterion : MaximalStatement.{uA, uM} := by
  intro A M _ _ _
  rw [accCriterion A M, WellFoundedGT, WellFounded.wellFounded_iff_has_min]

/-- The eventually constant increasing-sequence criterion. -/
theorem chainCriterion : ChainStatement.{uA, uM} := by
  intro A M _ _ _
  rw [accCriterion A M, wellFoundedGT_iff_monotone_chain_condition]

/-- The three criteria, in their statement's prescribed order. -/
theorem integerOriginalSubmoduleNoetherian :
    IntegerOriginalSubmoduleNoetherianStatement.{uA, uM} :=
  ⟨accCriterion, maximalCriterion, chainCriterion⟩

end Langlands.Algebra.IntegerOriginalSubmoduleNoetherian
