import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
/-!
# Fixed-level finiteness of compact-coefficient classes on `G°`

Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16, page 41, for the determinant-unit
subgroup `G°` of a product Levi: every compact open subgroup of `G°` has a nonzero fixed
vector in only finitely many isomorphism classes of irreducible smooth representations
with compactly supported smooth dual coefficients.
-/

namespace Langlands.AllField

universe uF uV

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation normalizedAbs_eq_one_iff
open Langlands.AllField.CuspidalSupport

/-- Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16: fixed-level finiteness of
compact-coefficient classes on the determinant-unit subgroup of a product Levi. -/
theorem compactCoefficientFixedLevelFiniteness :
    CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV} :=
  compactCoefficientFixedLevelFiniteness_of_cornerStructure determinantUnitCornerStructure
    sandwichSimpleModuleDimensionBound

end CuspidalSupport

end Langlands.AllField
