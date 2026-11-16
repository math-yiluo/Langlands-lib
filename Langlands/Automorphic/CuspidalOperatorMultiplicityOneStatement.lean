import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Multiplicity one for actual cuspidal operator realizations

Two actual irreducible cuspidal operator realizations of `GL_(r+1)` over a number field
that are equivalent, for the finite, compact and differential operators together, are the
same subspace of automorphic functions: an irreducible representation occurs at most once
in the space of cusp forms (Piatetski-Shapiro 1979, Shalika 1974; Cogdell 2004, p.202).
No proof is given here.
-/

noncomputable section

universe u

namespace Langlands.Automorphic

open Langlands.Global

/-- **Multiplicity one** (Cogdell 2004, p.202, after Piatetski-Shapiro and Shalika). If two
actual irreducible cuspidal operator realizations `T` and `T'` of `GL_(r+1)` over a number
field are equivalent, then they have the same underlying subspace of automorphic
functions. -/
def CuspidalOperatorMultiplicityOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : CuspidalOperatorRealization F r),
    Nonempty (T.Equivalence T') → T.realization = T'.realization

end Langlands.Automorphic
