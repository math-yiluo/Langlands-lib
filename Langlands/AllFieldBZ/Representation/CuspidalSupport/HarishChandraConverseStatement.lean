import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraStatement
import Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviHarishChandraConverseTheorem LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF uV

/-- BZ76 Theorem 3.21, (4) implies (1), with the empty-product rank-zero extension.
The coefficient condition uses the smooth dual of the restricted action. -/
def LeviHarishChandraConverseTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      HasCompactSmoothDualCoefficients
        (determinantUnitRestriction T B A.representation) →
          IsLeviQuasicuspidal B A.representation

end Langlands.AllFieldBZ.CuspidalSupport
