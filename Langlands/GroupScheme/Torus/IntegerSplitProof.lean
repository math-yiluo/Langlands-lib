import Langlands.GroupScheme.Torus.IntegerSplitStatement
import Langlands.GroupScheme.Torus.IntegerMultiplicativeTypeReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialProof
import Langlands.GroupScheme.Torus.RelativeDiagonalizableSplit
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Every torus over the integers is split -/

universe u

namespace Langlands.GroupScheme

/-- Every torus over the lifted integer spectrum is split
(Conrad, *Reductive group schemes* (2014), Corollary B.3.6, p. 293). -/
theorem integerTorusSplit : IntegerTorusSplitStatement.{u} := by
  intro T hT
  have hdiag :=
    RelativeMultiplicativeType.integer_isDiagonalizable_of_normalIsotrivial
      multiplicativeTypeNormalIsotrivial T hT.isMultiplicativeType
  exact hT.isSplitTorus_of_isDiagonalizable hdiag

end Langlands.GroupScheme
