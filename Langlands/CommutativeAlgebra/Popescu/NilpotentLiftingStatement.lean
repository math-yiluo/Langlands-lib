import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Over

/-! # Lifting smooth factorizations along a nilpotent ideal -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Proposition 16.5.3 (07CM): let `R → Λ` be flat and `I ⊆ R` nilpotent. If
`Λ / IΛ` has property PT over `R / I`, then `Λ` has property PT over `R`. Property
PT is used in its mapping form `HasSmoothFactorizations`. -/
def NilpotentLiftingStatement : Prop :=
  ∀ (R Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ] (I : Ideal R),
    IsNilpotent I → Module.Flat R Λ →
      HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) →
        HasSmoothFactorizations R Λ

end Langlands.CommutativeAlgebra.Popescu
