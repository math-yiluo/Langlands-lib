import Langlands.Algebra.NondegenerateModuleCompletenessStatements
import Langlands.Algebra.NondegenerateModuleProducts
import Langlands.Algebra.NonUnitalModuleDirectSum
import Langlands.CategoryTheory.RenardCompletenessLimits

/-! Completeness and cocompleteness proofs for the first assertion of Renard I.6. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateModuleCompletenessProof

open NondegenerateModuleCompletenessStatements

universe uA uI uM

/-- The concrete nondegenerate product fans give all index-sized products. -/
theorem complete : CompleteStatement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  exact hasProducts_of_limit_fans
    (fun P => NondegenerateModuleProducts.fan.{uA, uI, uM} P hA)
    (fun P => NondegenerateModuleProducts.fanIsLimit.{uA, uI, uM} P hA)

/-- The actual finite-support direct-sum cofans give all index-sized coproducts. -/
theorem cocomplete : CocompleteStatement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  exact hasCoproducts_of_colimit_cofans
    (fun P => NonUnitalModuleDirectSum.cofan.{uA, uI, uM} hA P)
    (fun P => NonUnitalModuleDirectSum.cofanIsColimit.{uA, uI, uM} hA P)

/-- Abelian equalizers and actual products give every diagram-sized limit. -/
theorem allLimits : AllLimitsStatement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  exact Langlands.Renard.sourceCompleteHasLimits.{uI}
    (NondegenerateModuleCat.{uA, max uI uM} A) (complete A hA)

/-- Abelian coequalizers and actual sums give every diagram-sized colimit. -/
theorem allColimits : AllColimitsStatement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  exact Langlands.Renard.sourceCocompleteHasColimits.{uI}
    (NondegenerateModuleCat.{uA, max uI uM} A) (cocomplete A hA)

/-- The four actual-category completeness and cocompleteness conclusions. -/
theorem completenessAssertions : CompletenessAssertions.{uA, uI, uM} :=
  ⟨complete, cocomplete, allLimits, allColimits⟩

example : CompleteStatement.{uA, uI, uM} := complete.{uA, uI, uM}
example : CocompleteStatement.{uA, uI, uM} := cocomplete.{uA, uI, uM}
example : AllLimitsStatement.{uA, uI, uM} := allLimits.{uA, uI, uM}
example : AllColimitsStatement.{uA, uI, uM} := allColimits.{uA, uI, uM}
example : CompletenessAssertions.{0, 1, 0} := completenessAssertions.{0, 1, 0}
example : CompletenessAssertions.{1, 0, 0} := completenessAssertions.{1, 0, 0}

end Langlands.Algebra.NondegenerateModuleCompletenessProof
