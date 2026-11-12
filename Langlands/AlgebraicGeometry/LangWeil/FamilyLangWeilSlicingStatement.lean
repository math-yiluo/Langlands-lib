import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement
import Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplaneStatement

/-!
# The induction step of the uniform Lang–Weil estimate by hyperplane slicing

The uniform Lang–Weil estimate in fibre dimension `d + 1` implies it in fibre dimension `d + 2`,
given Bertini's theorem for the generic hyperplane section and the uniform upper bound for point
counts in families.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Bertini's theorem for the generic hyperplane section (`BertiniGenericHyperplaneStatement`)
and the uniform point-count upper bound in families (`FamilyPointUpperBoundStatement`) imply
that, for every `d : ℕ`, the uniform Lang–Weil estimate in fibre dimension `d + 1` implies the
estimate in fibre dimension `d + 2`. -/
def FamilyLangWeilSlicingStatement : Prop :=
  BertiniGenericHyperplaneStatement.{u} → FamilyPointUpperBoundStatement.{u} →
    ∀ d : ℕ, FamilyLangWeilInDimension.{u} (d + 1) → FamilyLangWeilInDimension.{u} (d + 2)

end Langlands.AlgebraicGeometry.LangWeil
