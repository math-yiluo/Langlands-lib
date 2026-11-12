import Langlands.Algebra.NonUnitalModuleCornerSimpleStatements
import Langlands.Algebra.NonUnitalModuleCornerInductionProof
import Langlands.Algebra.IdempotentAnnihilatorComparisons

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open NonUnitalModuleCorner NonUnitalModuleCornerInduction
open NonUnitalModuleCornerSimpleStatements

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uW

/-- The canonical comparison is the composite of (I.3.2.1) and (I.3.2.2). -/
def fixedQuotientEquivalence {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (W : Type uW) [AddCommGroup W] [Module (Idempotent.Corner e) W] :
    W ≃ₗ[Idempotent.Corner e] FixedPart e (annihilatorQuotientCarrier e (Tensor e W)) :=
  (fixedPartEquivalence e W).trans
    (IdempotentAnnihilatorComparisons.fixedProjectionEquiv e (Tensor e W))

/-- The entire comparison uses the prescribed pure tensor and quotient projection. -/
theorem fixedPartInducedQuotient :
    FixedPartInducedQuotientStatement.{uA, uW} := by
  intro A _ e W _ _
  exact ⟨fixedQuotientEquivalence e W, fun _ => rfl⟩

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
