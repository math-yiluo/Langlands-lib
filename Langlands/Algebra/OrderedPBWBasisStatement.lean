import Langlands.Algebra.OrderedPBWMonomials
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # The finite-basis Poincare–Birkhoff–Witt proposition over an arbitrary field -/

universe u v

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

/-- The ordered powers of every supplied finite basis are linearly independent and span
the actual universal enveloping algebra, over a field of any characteristic. -/
def OrderedPBWBasisStatement : Prop :=
  ∀ (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (n : ℕ) (b : Module.Basis (Fin n) k L),
    LinearIndependent k (orderedPBWMonomial b) ∧
      Submodule.span k (Set.range (orderedPBWMonomial b)) = ⊤

end Langlands.Algebra.UniversalEnveloping
