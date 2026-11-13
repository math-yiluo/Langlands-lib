import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence

/-! # A minimal generating set of the maximal ideal of a regular local ring is regular -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Algebra Lemma 10.106.3 (00NQ): in a regular local ring `R`, a minimal set of generators
`x₁, …, x_d` of the maximal ideal is a regular sequence. A minimal generating set is a generating
family indexed by `Fin d` with `d` the least number of generators (`spanFinrank`). -/
def RegularLocalParametersStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (x : Fin (IsLocalRing.maximalIdeal R).spanFinrank → R),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R →
    RingTheory.Sequence.IsRegular R (List.ofFn x)

end Langlands.CommutativeAlgebra.Popescu
