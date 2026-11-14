import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraStatement
import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF uV

/-- The open determinant-unit subgroup does not change smooth dual vectors. -/
def DeterminantUnitSmoothDualStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (ℓ : Module.Dual ℂ V),
      IsSmoothVector (determinantUnitRestriction T B ρ).dual ℓ ↔
        IsSmoothVector ρ.dual ℓ

/-- The rank-zero instance of the full Harish-Chandra target. -/
def LeviHarishChandraRankZeroStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (B : BlockShape 0),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

end Langlands.AllFieldBZ.CuspidalSupport
