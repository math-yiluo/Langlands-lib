import Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility

/-!
# The two halves of the compatibility of Henniart's candidate with cyclic base change

`CandidateBaseChangeCompatibilityStatement` (interface E3 for the Library's
candidate) asks, for every cyclic prime-degree step `M/L`, for one weak cyclic
base change `Ch` with (CI1), and for (CI2) of the candidate over `M`. (CI2) does
not involve `Ch`. This module separates the two halves, each with candidate
existence as its premise:

* `CandidateGaloisEquivarianceReductionStatement`: candidate existence implies
  (CI2) for every step. This half is local: it is expected from transport of
  structure along the automorphism of `M` given by an element of `W_L`.
* `CandidateCompatibleWeakBaseChangeReductionStatement`: candidate existence
  implies that every step has a weak cyclic base change with (CI1). This half is
  global.

Candidate existence and the two halves together give
`CandidateBaseChangeCompatibilityStatement`: the map of the second half is the
witness, and the first half supplies (CI2). Proposition definitions only.
-/

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence Numerical

/-- Candidate existence implies (CI2) for every cyclic prime-degree step: in every
rank where the candidate over `M` is defined, it sends the conjugate of `τ` by
`w ∈ W_L` to the Galois conjugate of the candidate image of `τ` by the image of
`w` in `Gal(M/L)`. -/
def CandidateGaloisEquivarianceReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p),
      IsCandidateGaloisEquivariant.{uK, uW, uV} S

/-- Candidate existence implies that every cyclic prime-degree step has one weak
cyclic base change `Ch` with (CI1): in every rank where the candidates are
defined, `Ch` sends the candidate image of a Weil class over `L` to the multiset
of the candidate images of the constituents of its restriction to `W_M`. -/
def CandidateCompatibleWeakBaseChangeReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p),
      ∃ Ch : CyclicBaseChangeMap.{uK, uV} S,
        IsWeakCyclicBaseChange S Ch ∧ IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch

end Langlands.Henniart
