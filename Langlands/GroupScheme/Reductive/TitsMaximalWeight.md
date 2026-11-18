# The Tits class of a maximal simple weight

This module proves a matrix-coordinate counterpart, needed for the Tits
obstruction, of the multiplicity-one maximal-weight case of Proposition 3.4
(Tits also allows nonmaximal weights; see
`Reductive/HighestWeightMaximalSubquotient`) together with the characterization in
Corollary 3.5 of Tits, *Représentations linéaires irréductibles d'un groupe
réductif sur un corps quelconque*, J. reine angew. Math. 247 (1971),
pp. 204–205 (`α(λ) = [E]` when `G` has an `E`-representation with `λ` as a
simple weight). The implementation (adapted idempotents, compressions and
corners of twisted-fixed algebras) is this development's own. Let `ρ` be a representation of `G_K` with Galois
intertwiners `P σ : ρ → ρ^σ`, and let `B` be a twisted-fixed central simple
`k`-form containing its Tits algebra. If a star-fixed weight `ν` is maximal
among the weights of `ρ` and has multiplicity one, then the Tits obstruction
of `ν` is the class of `B`. For a representation defined over `k`, one may
take `P σ = 1` and `B = M_n(k)`, and the obstruction of such a weight
vanishes; this corresponds to the case `D = k`.

## Trivial twisting (`Algebra.GaloisTwistedMatrix`)

- `groundMatrices k`: the matrices with entries in `k`, as a `k`-subalgebra of
  `M_n(K)`; it is the range of the entrywise map `M_n(k) → M_n(K)`.
- `mapMatrix_injective`, `groundMatrices_le_twistedFixed_one` (entries in `k`
  are fixed by `K ≃ₐ[k] K`), `span_groundMatrices` (the matrix units are in
  `groundMatrices k`).
- `twistedFixed_one_eq_groundMatrices`: for `K/k` Galois,
  `twistedFixed (fun _ => 1) = groundMatrices k`. One inclusion is the
  previous lemma. Equality follows by dimension: the left side has dimension
  at most `n²` (`finrank_twistedFixed_le`), and the right side has dimension
  `n²`.
- `twistedFixedOneEquiv : twistedFixed (fun _ => 1) ≃ₐ[k] M_n(k)` and
  `span_twistedFixed_one`.
- `classOf_toCSA_one`: the central simple algebra `toCSA` for the trivial
  twisting has class `0`. It is isomorphic to
  `matrix (groundField k) (card n)` after reindexing, so `classOf_matrix` and
  `classOf_groundField` apply.

## The maximal-weight case of Proposition 3.4 (`GaloisPinningData`)

- `titsCSAOf_isBrauerEquivalent_of_maximal`. Hypotheses:
  - `ρ` is a representation on a nonempty `N`, with invertible intertwiners
    `P σ : ρ → ρ^σ`;
  - `B ≤ twistedFixed P` has `K`-span `M_N(K)` and contains `titsAlgebra ρ`;
  - `ν` is star-fixed, `ρ_ν` is a line, and `ν` is maximal among the weights
    of `ρ`;
  - `ρ'` is any representation with `IsHighestWeight ρ' ν` (in particular
    irreducible). The representation `ρ` itself need not be irreducible.

  Conclusion: `titsCSAOf ρ'` is Brauer equivalent to `toCSA P B`. The proof
  follows the additivity theorem of `Reductive/TitsAdditivity`:
  1. The flag `highestRadical ρ ν ≤ highestGenerated ρ ν` is twisted-stable
     (`Reductive/HighestWeightTwistedStability`), so
     `exists_adapted_idempotent` gives an adapted idempotent `f ∈ B`.
  2. `isHighestWeight_of_maximal` shows that the subquotient has highest
     weight `ν`.
  3. `titsAlgebra_quot_eq_compressed` identifies its Tits algebra with a
     compression of `B`.
  4. The corner theorem `isBrauerEquivalent_toCSA_compressed` gives the class
     of `B`, and `titsCSAOf_isBrauerEquivalent` gives independence of `ρ'`.
- `titsObstructionValue_of_maximal`: under the same hypotheses (with
  `hspan`), `titsObstructionValue ν = classOf (toCSA P B)`. The weight `ν` is
  dominant by `isDominantWeight_of_maximal`, so `titsObstructionValue_eq_classOf`
  applies to the subquotient.
- `IsGaloisRational ρ`: every Galois twist of `ρ` has the universal matrix of
  `ρ`. Scalar extensions of representations over `k` are the intended
  examples. `IsGaloisRational.intertwines_one`: then `1 : ρ → ρ^σ` intertwines
  (`intertwines_iff_universalMatrix`).
- `titsObstructionValue_eq_zero_of_rational`: for a Galois-rational `ρ` and a
  star-fixed maximal weight `ν` of multiplicity one,
  `titsObstructionValue ν = 0`. Take `P = 1` and `B = twistedFixed 1`, and use
  `classOf_toCSA_one`.
