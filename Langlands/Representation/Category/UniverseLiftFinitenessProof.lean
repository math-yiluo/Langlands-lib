import Langlands.Representation.Category.UniverseLiftFinitenessStatement

/-! # Proof of actual finiteness invariance under a universe lift -/

set_option autoImplicit false

namespace Langlands.SmoothRep

universe uX uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (A : SmoothRep.{0, uG, uV} ℂ G)

/-- Finite generation over the actual group algebra is invariant under
raising the carrier universe. -/
theorem moduleFinite_universeLift_iff :
    Module.Finite (MonoidAlgebra ℂ G)
        (universeLift.{uX} A).representation.asModule ↔
      Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule := by
  constructor
  · intro h
    let := h
    exact Module.Finite.of_surjective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (universeLiftEquiv.{uX} A).symm.toIntertwiningMap)
      (universeLiftEquiv.{uX} A).symm.surjective
  · intro h
    let := h
    exact Module.Finite.of_surjective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (universeLiftEquiv.{uX} A).toIntertwiningMap)
      (universeLiftEquiv.{uX} A).surjective

/-- Actual group-algebra finite length is invariant under raising the
carrier universe. -/
theorem hasFiniteLength_universeLift_iff :
    (universeLift.{uX} A).HasFiniteLength ↔ A.HasFiniteLength := by
  constructor
  · intro h
    exact IsFiniteLength.of_surjective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (universeLiftEquiv.{uX} A).symm.toIntertwiningMap)
      (universeLiftEquiv.{uX} A).symm.surjective
  · intro h
    exact IsFiniteLength.of_surjective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (universeLiftEquiv.{uX} A).toIntertwiningMap)
      (universeLiftEquiv.{uX} A).surjective

end Langlands.SmoothRep

namespace Langlands

/-- The two actual group-algebra finiteness predicates survive arbitrary
carrier universe lifting. -/
theorem universeLiftFiniteness.{uX, uG, uV} :
    UniverseLiftFinitenessStatement.{uX, uG, uV} := by
  intro G _ _ A
  exact ⟨SmoothRep.moduleFinite_universeLift_iff A,
    SmoothRep.hasFiniteLength_universeLift_iff A⟩

end Langlands
