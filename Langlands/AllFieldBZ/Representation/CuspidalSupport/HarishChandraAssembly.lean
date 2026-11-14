import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraConverseProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraForwardProof
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraAssembly`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraAssembly` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem DeterminantUnitSmoothDualStatement LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem NonassociatedJacquetSubquotientsTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
universe uF uV

/-- Harish-Chandra's compact-coefficient characterization on every product Levi. -/
theorem leviHarishChandraTheorem : LeviHarishChandraTheorem.{uF, uV} := by
  intro F T n B
  let := T.topology
  intro A
  cases n with
  | zero => exact leviHarishChandraRankZero F T B A
  | succ n =>
    exact ⟨HarishChandra.hasCompactSmoothDualCoefficients_of_isLeviQuasicuspidal_of_cartan
      GeneralLinear.Cartan.cartanDecomposition T B A.representation A.isSmooth,
      leviHarishChandraConverseTheorem F T (n + 1) B A⟩

end Langlands.AllFieldBZ.CuspidalSupport
