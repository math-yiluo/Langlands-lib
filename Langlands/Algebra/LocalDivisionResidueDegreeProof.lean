import Langlands.Algebra.LocalDivisionResidueDegreeStatement
import Langlands.Algebra.LocalDivisionReducedDegree

/-! The exact local residue-degree proposition. -/

namespace Langlands.CentralDivision

universe u

/-- The actual residue extension has reduced degree over every nonarchimedean local field. -/
theorem localResidueDegree : LocalResidueDegreeStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _
  exact localDivisionResidue_finrank_eq_reducedDegree K D

end Langlands.CentralDivision
