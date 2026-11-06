import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperStatement
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointProof

/-!
# Henselian valued fields of characteristic zero are algebraically closed in their completion

The characteristic-zero case of Conrad's remark after Corollary 5.12.
-/

universe u

open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- In characteristic zero every algebraic element is separable, so the algebraic closure
of a henselian valued field in its completion is its separable closure, which is trivial. -/
theorem henselianCharZeroAlgebraicallyClosedInCompletion :
    HenselianCharZeroAlgebraicallyClosedInCompletionStatement.{u} := by
  intro K _ hK _
  rw [eq_bot_iff, ← henselianSeparablyClosedInCompletion K hK]
  intro x hx
  rw [mem_separableClosure_iff]
  exact (minpoly.irreducible (mem_algebraicClosure_iff.mp hx).isIntegral).separable

end Langlands.AlgebraicGeometry.AlgebraicSpace
