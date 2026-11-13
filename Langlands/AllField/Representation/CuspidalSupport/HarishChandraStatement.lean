import Langlands.Representation.CuspidalSupport.HarishChandraStatement
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit
/-! Harish-Chandra's compact-coefficient criterion on actual product Levis. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

/-- BZ76 Theorem 3.21, (1) iff (4), with the empty-product rank-zero extension.
The coefficient condition uses the smooth dual of the restricted action. -/
def LeviHarishChandraTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

end Langlands.AllField.CuspidalSupport
