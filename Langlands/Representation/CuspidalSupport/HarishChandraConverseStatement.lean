import Langlands.Representation.CuspidalSupport.HarishChandraStatement

/-! Compact coefficients on the determinant-unit subgroup imply quasicuspidality. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- BZ76 Theorem 3.21, (4) implies (1), with the empty-product rank-zero extension.
The coefficient condition uses the smooth dual of the restricted action. -/
def LeviHarishChandraConverseTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      HasCompactSmoothDualCoefficients
        (determinantUnitRestriction T B A.representation) →
          IsLeviQuasicuspidal B A.representation

end Langlands.CuspidalSupport
