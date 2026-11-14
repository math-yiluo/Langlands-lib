import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF uV

/-- For every positive-rank product Levi over an actual p-adic field, each
compact open subgroup of its determinant-unit subgroup `G°` has a nonzero fixed
vector in only finitely many isomorphism classes of irreducible smooth complex
representations of `G°` with compact smooth-dual coefficients. -/
def CompactCoefficientFixedLevelFinitenessTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ K : OpenSubgroup (determinantUnitSubgroup T B),
      IsCompact (K : Set (determinantUnitSubgroup T B)) →
        (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite

end Langlands.AllFieldBZ.CuspidalSupport
