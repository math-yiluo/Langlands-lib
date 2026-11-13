import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilZeroProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilCurveProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilSlicingProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundProof
import Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplaneProof

/-!
# Dimension induction for uniform family Lang–Weil

The existing zero, curve and slicing results imply all dimensions. The upper-bound
and Bertini premises are supplied by their published proofs.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The plane-curve estimate suffices for the uniform estimate in every fibre dimension. -/
theorem familyLangWeilOfPlaneCurve : FamilyLangWeilOfPlaneCurveStatement.{u} := by
  intro hPlane d
  have hPositive : ∀ n : ℕ, FamilyLangWeilInDimension.{u} (n + 1) := by
    intro n
    induction n with
    | zero => exact familyLangWeilCurve hPlane familyPointUpperBound
    | succ n ih =>
      exact familyLangWeilSlicing
        BertiniGenericHyperplane.bertiniGenericHyperplaneStatement
        familyPointUpperBound n ih
  cases d with
  | zero => exact familyLangWeilZero
  | succ n => exact hPositive n

end Langlands.AlgebraicGeometry.LangWeil
