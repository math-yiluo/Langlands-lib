import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraStatement
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

/-- The open determinant-unit subgroup does not change smooth dual vectors. -/
def DeterminantUnitSmoothDualStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F) V) (ℓ : Module.Dual ℂ V),
      IsSmoothVector (determinantUnitRestriction T B ρ).dual ℓ ↔
        IsSmoothVector ρ.dual ℓ

/-- The rank-zero instance of the full Harish-Chandra target. -/
def LeviHarishChandraRankZeroStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (B : BlockShape 0),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

end Langlands.AllField.CuspidalSupport
