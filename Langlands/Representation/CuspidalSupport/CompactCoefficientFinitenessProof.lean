import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
import Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
import Langlands.Algebra.SandwichDimensionBoundProof

/-!
# Fixed-level finiteness of compact-coefficient classes on `G°`

Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16, page 41, for the determinant-unit
subgroup `G°` of a product Levi: every compact open subgroup of `G°` has a nonzero fixed
vector in only finitely many isomorphism classes of irreducible smooth representations
with compactly supported smooth dual coefficients.
-/

namespace Langlands

universe uF uV

namespace CuspidalSupport

/-- Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16: fixed-level finiteness of
compact-coefficient classes on the determinant-unit subgroup of a product Levi. -/
theorem compactCoefficientFixedLevelFiniteness :
    CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV} :=
  compactCoefficientFixedLevelFiniteness_of_cornerStructure determinantUnitCornerStructure
    sandwichSimpleModuleDimensionBound

end CuspidalSupport

end Langlands
