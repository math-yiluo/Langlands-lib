import Langlands.Global.Factors.CuspidalPairFactorData

/-!
# Strong multiplicity one for actual cuspidal realizations of `GL_(r+1)`

Getz–Hahn (2024), Theorem 11.7.2 (Jacquet–Shalika 1981, *Euler products I*,
Theorem 4.8 and Corollary 4.10), for actual cuspidal realizations of `GL_(r+1)` over a
number field. If the finite local components of spectral presentations of two such
realizations are isomorphic at all finite places outside a finite set, then the two
realizations are equivalent as full operator realizations. The local components are
the canonical p-adic classes `localClass` of the presentations. See the paired
Markdown for the source, the treatment of the infinite places and the scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)

/-- **Strong multiplicity one** (Getz–Hahn 2024, Theorem 11.7.2). Let `T`, `T'` be
actual cuspidal realizations of `GL_(r+1)` over a number field `F`, with spectral
presentations `P`, `P'` whose finite local components are irreducible and admissible.
If the local components of `P` and `P'` have the same class at every finite place
outside a finite set `S`, then `T` and `T'` have the same full operator class. -/
def CuspidalStrongMultiplicityOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)),
    (∀ v ∉ S, localClass P h v = localClass P' h' v) →
    T.isoClass = T'.isoClass

end Langlands.Global
