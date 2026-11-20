# Waldspurger's compact and split-central quotient normalization

Waldspurger, *La formule de Plancherel pour les groupes p-adiques*, I.1,
printed pp. 238 and 240 (PDF pp. 4 and 6), fixes a maximal split torus
and a maximal compact subgroup at a special point in its apartment. Haar
measure on each closed algebraic subgroup gives its trace in that same
compact mass one. III.1 (3), printed p. 265 (PDF p. 31), uses the quotient
measure for the inverse formal degree, which scales the product form in
V.2, printed p. 293 (PDF p. 59).

`IsSourceCompactAt` specifies the maximal compact as the actual norm-one
fixer of a special vertex in the `ord_F`-compatible valuation apartment
of the displayed maximal split torus. `IsSourceCompactFor` allows that
torus to be specified through a factorization of the cocharacter that
presents the Levi. The torus is then contained in that centralizer.
Theorems `IsSourceCompactAt.inner`, `IsSourceCompactFor.inner`, and
`isSourceCompactFor_conjugate` transport the same apartment, special point
and compact through the actual inner isomorphism. The proofs use the
published transport of valued apartments and their norm-one fixers.

`quotientTrace` is the image of the actual compact Levi trace under the
quotient map by the split center. `IsNormalizedQuotientHaar` requires
that image to have mass one. To derive this scale from Weil compatibility,
`normalizedQuotientHaar_of_weil` uses the published compact-open orbit
integral with the constant test on the identity orbit. The two trace
masses in the Weil formula are one. The resulting mass on the image is
one as well. For a closed central subgroup, `normalizedQuotientHaar_iff_eq_weil`
uses left invariance of the transferred Weil measure and the exact
compact mass to identify it with the displayed Haar measure. Haar
uniqueness also gives `IsNormalizedQuotientHaar.eq_of_haar`.

`IsSourceQuotientHaar` applies that scale to the literal dynamic Levi.
`normalizedQuotientHaar_map_iff` follows by taking the preimage of the
compact quotient trace. In `isSourceQuotientHaar_conjugate`, membership
in the original compact trace is equivalent to membership of the
conjugated point in the conjugate compact trace. The given quotient
Haar pushforward thus retains the source scale on both quotients.
