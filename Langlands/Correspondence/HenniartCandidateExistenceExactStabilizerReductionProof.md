# Henniart's candidate existence from Harris's exact-stabilizer proposition

`Langlands.Henniart.candidateExistenceExactStabilizerReduction` proves
`CandidateExistenceExactStabilizerReductionStatement` at independent
universes `uK`, `uW`, `uP`, `uE`, and `uQ`. It follows the assembly in the
Library's `HenniartCandidateExistenceReductionProof` using the exact-stabilizer
globalization reduction.

The local class formation hypothesis supplies invariant families with
arithmetic normalization. `globalFundamentalClassStatement` gives the
arithmetic fundamental class family `c` needed for the relative Weil groups.
`henniartGlobalizationExactStabilizerReduction`, applied to the given Harris
and supercuspidal induction premises and the four published local inputs,
then supplies a number-field extension `E/F`, a place `v`, a completion
isomorphism `f`, and a witness that the relative Weil image covers every
unitary Weil class factoring through `q`.

The proof chooses the standard finite additive component at `v` and applies
the certified pole comparisons there. `relativePolePairing` supplies the
positive isometry `T` of the generated lattices. The candidate is
`henniartCompositeMap F E c v h K f T`, with the stated properties provided by
the composite-map premise. `continuousRestrict_completionWeilTransport_eq_iff`
turns each coverage witness into an equality in the transported unitary Weil
lattice, giving membership in the candidate's domain.

This assembly is the Library's relative formulation of Henniart 2000,
Théorème 3.1, Lemme 2.8 and §§3.7–3.8, pp. 448 and 451
(`henniart-2000-simple-proof`). The globalization takes Harris 1998,
Proposition 4.8, p. 201, with condition (4.12), p. 204
(`harris-1998-local-langlands`).
