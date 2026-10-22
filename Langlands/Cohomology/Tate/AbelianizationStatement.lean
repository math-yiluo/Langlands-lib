import Langlands.Cohomology.Tate.LowDegree
import Langlands.Cohomology.Tate.TransferDefinitions

universe u

namespace Langlands.Tate

/-- Integral degree-minus-two corestriction and restriction are inclusion and transfer. -/
def AbelianizationLaws : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)],
    (∀ x : tateCohomology (integralTrivial H) (-2),
      integralMinusTwoEquiv G (corestriction H (integralTrivial G) (-2) x) =
        abelianizationInclusion H (integralMinusTwoEquiv H x)) ∧
    (∀ x : tateCohomology (integralTrivial G) (-2),
      integralMinusTwoEquiv H (restriction H (integralTrivial G) (-2) x) =
        abelianizationTransfer H (integralMinusTwoEquiv G x))

end Langlands.Tate
