import Langlands.Algebra.NonUnitalModuleCornerEquivalenceCriterionProof

/-!
# Renard I.3.2: the simple-module correspondence and corner equivalence criterion

The exact published aggregate, retaining independent universes and the original objects.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open NonUnitalModuleCornerSimpleStatements

universe uA uM uW

/-- The three clauses of the Theorem of I.3.2. -/
theorem cornerEquivalence : CornerEquivalenceStatement.{uA, uM} :=
  ⟨cornerEquivalenceCriterion, generatedCategoryAbelian, cornerInductionInverse⟩

/-- Renard I.3.2, Proposition and Theorem, on the published original-action objects. -/
theorem statements : Statements.{uA, uM, uW} :=
  ⟨simpleCorrespondence, cornerEquivalence⟩

example : Statements.{uA, uM, uW} := statements.{uA, uM, uW}
example : Statements.{2, 0, 1} := statements.{2, 0, 1}
example : Statements.{0, 2, 1} := statements.{0, 2, 1}
example : Statements.{1, 0, 2} := statements.{1, 0, 2}

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
