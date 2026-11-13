import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.RegularRingMaps

/-! # Popescu's theorem over a base field -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Popescu's theorem when the base is a field (the case to which Stacks 07GC is
reduced by Lemma 8.4, 07F5): for a regular algebra map from a field `k` to a
Noetherian ring `Λ`, every `k`-algebra map from a finitely presented
`k`-algebra to `Λ` factors through a smooth `k`-algebra. -/
def PopescuFieldCaseStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [IsNoetherianRing Λ] [Algebra k Λ],
    RegularAlgebra k Λ → HasSmoothFactorizations k Λ

end Langlands.CommutativeAlgebra.Popescu
