import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Geometric regularity and the map `H₁(L_{κ/k}) → 𝔪/𝔪²` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks More on Algebra, Proposition 15.36.1 (07E5), implication (1) ⇒ (3), at a prime of a
geometrically regular algebra: let `k` be a field of characteristic `p > 0`, `Λ` a Noetherian
geometrically regular `k`-algebra and `q` a prime of `Λ`, with `A = Λ_q` and `K = κ(q)`. Then the
canonical map `H₁(L_{K/k}) → H₁(L_{K/A})` (`H₁(L_{K/A}) = 𝔪/𝔪²`) is injective. -/
def GeometricRegularityH1InjectiveStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ → ∀ (q : Ideal Λ) [q.IsPrime],
      Function.Injective (Algebra.H1Cotangent.map k (Localization.AtPrime q) q.ResidueField
        q.ResidueField)

end Langlands.CommutativeAlgebra.Popescu
