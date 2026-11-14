import Langlands.Global.Factors.IsobaricAutomorphicRepresentation

/-!
# Automorphy of isobaric sums of cuspidal representations at every place

Getz–Hahn (2024), Theorem 10.7.5, at all places, for actual cuspidal realizations of
general linear groups over a number field. Let `π_1, …, π_k` be cuspidal realizations
of `GL_(m_i+1)` with total rank `r + 1`. There is an irreducible automorphic
subquotient `Q` of `GL_(r+1)` that is the isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` at every
place, in the sense of `IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum`. See
the paired Markdown for the sources, the scope and the relation to the finite-place
statement `CuspidalIsobaricRealizationStatement`.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

/-- **Automorphy of isobaric sums at every place** (Getz–Hahn 2024, Theorem 10.7.5).
Let `T i` (`i < k`) be actual cuspidal realizations of `GL_(m i + 1)` over a number
field `F`, with `∑ (m i + 1) = r + 1`, and spectral presentations whose finite local
components are irreducible and admissible. Then there is an irreducible automorphic
operator subquotient `Q` of `GL_(r+1)` that is the isobaric sum of the `T i` at every
place: at the finite places it contains the local isobaric sums of the local
components, and at the real and complex places the Langlands quotient of the ordered
union of the archimedean parameters of the `T i`. -/
def CuspidalIsobaricAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ), ∑ i, (m i + 1) = r + 1 →
    ∀ (T : ∀ i, CuspidalOperatorRealization F (m i))
      (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
      (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
      ∃ Q : IrreducibleOperatorSubquotient F r, Q.IsCuspidalIsobaricSum T P h

end Langlands.Global
