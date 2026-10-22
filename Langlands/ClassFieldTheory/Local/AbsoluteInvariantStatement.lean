import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.LocalField.Definitions

/-! # Existence of absolute local invariants compatible with restriction -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Absolute local degree-two cohomology admits invariant isomorphisms whose
restriction law is multiplication by the finite extension degree. -/
def AbsoluteInvariantExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ inv : ∀ F : PadicField.{u} p,
        absoluteCohomology F.Carrier 2 ≃+ RationalModIntegers,
      ∀ (F E : PadicField.{u} p) [Algebra F.Carrier E.Carrier]
        [IsScalarTower (Padic p) F.Carrier E.Carrier]
        [FiniteDimensional F.Carrier E.Carrier]
        [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
        [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
          (AlgebraicClosure E.Carrier)],
        ∀ x : absoluteCohomology F.Carrier 2,
          inv E (absoluteRestriction F.Carrier E.Carrier 2 x) =
            Module.finrank F.Carrier E.Carrier • inv F x

end Langlands.ClassFieldTheory.Local
