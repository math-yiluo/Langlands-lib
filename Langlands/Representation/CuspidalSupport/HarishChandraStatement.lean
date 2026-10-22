import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CompactCoefficient.Classes

/-! Harish-Chandra's compact-coefficient criterion on actual product Levis. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- BZ76 Theorem 3.21, (1) iff (4), with the empty-product rank-zero extension.
The coefficient condition uses the smooth dual of the restricted action. -/
def LeviHarishChandraTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation ↔
        HasCompactSmoothDualCoefficients
          (determinantUnitRestriction T B A.representation)

end Langlands.CuspidalSupport
