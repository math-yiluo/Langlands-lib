import Langlands.Representation.CuspidalSupport.FiniteRestrictionStatement
import Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction

/-! The finite determinant-unit restriction theorem for irreducible smooth Levi representations. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- BZ76 Lemma 3.26 in the reduced spanning form of the published statement. -/
theorem leviFiniteRestrictionTheorem : LeviFiniteRestrictionTheorem.{uF, uV} := by
  intro p hp F T n B
  exact FiniteRestriction.leviFiniteRestriction F T B

end Langlands.CuspidalSupport
