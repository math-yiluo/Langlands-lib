import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-! # A common strictly upper triangular basis for commuting nilpotent endomorphisms -/

namespace Langlands

universe uK uV uI

/-- Every family of pairwise commuting nilpotent endomorphisms of a
finite-dimensional vector space over an arbitrary field admits one basis indexed
by `Fin (Module.finrank K V)` in which every member of the family has a strictly
upper triangular matrix: the `i`-th coordinate of `N t (b j)` vanishes whenever
`j ≤ i`. The index type is arbitrary, possibly empty or infinite. This is a
statement, not a proof. -/
def CommutingNilpotentStrictUpperBasisStatement : Prop :=
  ∀ (K : Type uK) [Field K] (V : Type uV) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (I : Type uI) (N : I → Module.End K V),
    (∀ s t, Commute (N s) (N t)) →
    (∀ t, IsNilpotent (N t)) →
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ (t : I) (i j : Fin (Module.finrank K V)), j ≤ i → b.repr (N t (b j)) i = 0

end Langlands
