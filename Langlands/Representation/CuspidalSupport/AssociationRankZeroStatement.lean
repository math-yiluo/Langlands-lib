import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement

namespace Langlands.CuspidalSupport

universe uF uV uW

/-- The full association theorem restricted to the rank-zero boundary case,
with independent field and inducing carrier universes. -/
def CuspidalInductionAssociationRankZeroStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    CuspidalInductionAssociationTheorem.{uF, uV, uW} F T 0

end Langlands.CuspidalSupport
