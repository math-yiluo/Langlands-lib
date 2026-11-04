import Langlands.Representation.Category.UniverseLift

/-! # Actual group-algebra finiteness under a universe lift -/

set_option autoImplicit false

namespace Langlands

/-- Raising the carrier universe preserves finite generation and finite
composition length over the actual complex group algebra. -/
def UniverseLiftFinitenessStatement.{uX, uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    (Module.Finite (MonoidAlgebra ℂ G)
        (SmoothRep.universeLift.{uX} A).representation.asModule ↔
      Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule) ∧
    ((SmoothRep.universeLift.{uX} A).HasFiniteLength ↔ A.HasFiniteLength)

end Langlands
