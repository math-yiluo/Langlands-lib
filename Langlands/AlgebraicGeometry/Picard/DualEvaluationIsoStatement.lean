import Langlands.AlgebraicGeometry.ModuleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-!
# Canonical dual evaluation for locally free rank-one scheme modules

This file states the evaluation-isomorphism step for the existing canonical
evaluation map. It supplies no proof of that statement.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The canonical dual evaluation of every locally free rank-one module sheaf
on `X` is an isomorphism. This definition states the assertion. -/
def LocallyFreeRankOneDualEvaluationIsIsoStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    IsLocallyFreeRankOne M →
      CategoryTheory.IsIso (Langlands.Scheme.Modules.dualMonoidalEval M)

end Langlands.AlgebraicGeometry.Picard
