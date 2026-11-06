import Langlands.Algebra.OrderedPBWBasisStatement
import Langlands.Algebra.OrderedPBWRepresentation

/-! # Ordered finite-basis PBW over arbitrary fields -/

universe u v

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

/-- The actual ordered monomials of every finite Lie basis form a basis. -/
theorem orderedPBWBasis : OrderedPBWBasisStatement.{u,v} := by
  intro k _ L _ _ n b
  exact ⟨PBW.orderedPBWMonomial_linearIndependent b, orderedPBWMonomial_span b⟩

end Langlands.Algebra.UniversalEnveloping
