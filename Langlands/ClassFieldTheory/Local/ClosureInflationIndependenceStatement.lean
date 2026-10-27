import Langlands.ClassFieldTheory.Local.FiniteComparison
import Langlands.ClassFieldTheory.Local.RelativeH2Transport

/-! # Independence of closure inflation from the chosen isomorphism

A field `L` may be identified over `K` with a normal finite subfield of the
algebraic closure in more than one way. Transporting a relative degree-two
class along either identification and inflating gives the same absolute class.
-/

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- For two `K`-isomorphisms of `L` onto normal finite subfields of the
algebraic closure, transport followed by closure inflation gives the same
absolute degree-two class. -/
def ClosureInflationTransportIndependence : Prop :=
  ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E₁] [Normal K E₁] [FiniteDimensional K E₂] [Normal K E₂]
    (e₁ : L ≃ₐ[K] E₁) (e₂ : L ≃ₐ[K] E₂) (x : relativeCohomology K L 2),
    closureInflation K E₂ 2 (relativeH2Equiv e₂ x) =
      closureInflation K E₁ 2 (relativeH2Equiv e₁ x)

end Langlands.ClassFieldTheory.Local
