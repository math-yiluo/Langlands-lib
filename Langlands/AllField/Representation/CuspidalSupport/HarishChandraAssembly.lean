import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraConverseProof
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraForwardProof
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.AllField.CuspidalSupport

universe uF uV

/-- Harish-Chandra's compact-coefficient characterization on every product Levi. -/
theorem leviHarishChandraTheorem : LeviHarishChandraTheorem.{uF, uV} := by
  intro F _ T n B
  let := T.topology
  intro A
  cases n with
  | zero => exact leviHarishChandraRankZero F T B A
  | succ n =>
    exact ⟨Langlands.AllField.CuspidalSupport.HarishChandra.hasCompactSmoothDualCoefficients_of_isLeviQuasicuspidal_of_cartan
      GeneralLinear.Cartan.cartanDecomposition T B A.representation A.isSmooth,
      leviHarishChandraConverseTheorem F T (n + 1) B A⟩

end Langlands.AllField.CuspidalSupport
