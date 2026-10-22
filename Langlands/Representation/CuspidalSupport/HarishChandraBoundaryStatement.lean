import Langlands.Representation.CuspidalSupport.HarishChandraStatement

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- The open determinant-unit subgroup does not change smooth dual vectors. -/
def DeterminantUnitSmoothDualStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (ℓ : Module.Dual ℂ V),
      IsSmoothVector (determinantUnitRestriction T B ρ).dual ℓ ↔
        IsSmoothVector ρ.dual ℓ

/-- The rank-zero instance of the full Harish-Chandra target. -/
def LeviHarishChandraRankZeroStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (B : BlockShape 0),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

/-- Elementary boundary and convention checks needed by the full proof. -/
def HarishChandraBoundaryStatement : Prop :=
  DeterminantUnitSmoothDualStatement.{uF, uV} ∧
    LeviHarishChandraRankZeroStatement.{uF, uV}

end Langlands.CuspidalSupport
