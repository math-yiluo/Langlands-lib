import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraBoundaryStatement
import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uF uV uR uG

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraRankZero mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
/-- Smoothness is tested for the restricted dual itself. -/
theorem determinantUnitSmoothDual : DeterminantUnitSmoothDualStatement.{uF, uV} := by
  intro F T n B
  let := T.topology
  intro V _ _ ρ ℓ
  change IsSmoothVector (ρ.dual.comp (determinantUnitOpenSubgroup T B).toSubgroup.subtype) ℓ ↔ _
  exact isSmoothVector_restrict_open_iff ρ.dual (determinantUnitOpenSubgroup T B) ℓ

/-- Every coefficient on the empty product Levi has compact support. -/
theorem leviHarishChandraRankZero : LeviHarishChandraRankZeroStatement.{uF, uV} := by
  intro F T B
  let := T.topology
  intro A
  have hsize (i : Fin B.length) : B.size i ≤ 0 := by
    calc
      B.size i ≤ ∑ j, B.size j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = 0 := B.sum_eq
  let : IsEmpty (Fin B.length) := ⟨fun i => (Nat.not_lt_of_ge (hsize i)) (B.positive i)⟩
  have hq : IsLeviQuasicuspidal B A.representation := by
    intro S hS
    exact (hS (Subsingleton.elim _ _)).elim
  have hc : HasCompactSmoothDualCoefficients
      (determinantUnitRestriction T B A.representation) := by
    intro v ℓ _
    exact HasCompactSupport.of_compactSpace _
  exact ⟨fun _ => hc, fun _ => hq⟩

end CuspidalSupport
end Langlands.AllFieldBZ
