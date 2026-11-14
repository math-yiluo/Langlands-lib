import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.Over

/-! # Finiteness of `H₁(L_{κ(q)/k})` for geometrically regular algebras -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- A consequence of Stacks More on Algebra, Proposition 15.36.1 (07E5), (1) ⇒ (3): let `k` be a
field of characteristic `p > 0`, `Λ` a Noetherian geometrically regular `k`-algebra and `q` a prime
of `Λ`. Then `H₁(L_{κ(q)/k})` is a finite-dimensional `κ(q)`-vector space. -/
def GeometricRegularityH1FiniteStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ → ∀ (q : Ideal Λ) [q.IsPrime],
      Module.Finite q.ResidueField (Algebra.H1Cotangent k q.ResidueField)

end Langlands.CommutativeAlgebra.Popescu
