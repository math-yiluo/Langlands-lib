import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.HarishChandraStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF uV

/-- BZ76 Theorem 3.21, (1) iff (4), with the empty-product rank-zero extension.
The coefficient condition uses the smooth dual of the restricted action. -/
def LeviHarishChandraTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

end Langlands.AllFieldBZ.CuspidalSupport
