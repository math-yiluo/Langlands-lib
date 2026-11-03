import Langlands.GroupScheme.Dynamic.AdjointDeterminantFormulaStatement

/-! # Proof of the all-test formula for the actual adjoint determinant -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The constructed character is the determinant of the actual conjugation
differential, on every affine test and every scheme test. -/
theorem dynamicAdjointDeterminantFormula : DynamicAdjointDeterminantFormulaStatement.{u} := by
  intro R G P U χ iP iU hP hU _ _ d c
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T p u
    exact Dynamic.parabolicAdjointAction_act_comp hP hU p u
  · intro A p x
    exact (Dynamic.parabolicAdjointAction hP hU).finiteRepresentation_affineAction c A p x
  · intro A p
    exact Dynamic.adjointDeterminantCharacter_affinePoints hP hU c A p
  · intro T p
    exact (Dynamic.parabolicAdjointAction hP hU).determinantCharacter_eval c T p

end Langlands.GroupScheme
