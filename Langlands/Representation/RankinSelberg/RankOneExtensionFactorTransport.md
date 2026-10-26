# Certified-factor and zeta-value transport for rank-one extension

Author: Worker 469.

This is a derived construction using the published
`rankOneExtensionLowerToUpperEquiv` and the existing equivalence invariance
of Whittaker type, coefficient sets, zeta values and certified pair polynomials.
It supplies no new analytic comparison or factor-existence theorem.

`rankOneExtensionLowerToUpper` chooses an actual representation equivalence
from the published existence theorem. Its source is the actual canonical
normalized opposite induction of the reversed Shahidi family, with lower
ordered factors `(sigma,chi)`. Its target is exactly the canonical normalized
upper induction on `Shahidi.twoBlocks 1 (t+1)` with family `(chi,sigma)`.
Only the rank-one complex carrier is lifted to the universe of `sigma`.
The input representations are arbitrary smooth factors. The field, test
representation and second-factor carrier universes remain independent.

The choice uses `Classical.choice`; it has no prescribed formula for
evaluations of sections. Subsequent identities depend only on the resulting
intertwining equivalence. They do not identify the two upper block orders.

`rankOneExtensionInverseWhittakerSet_eq` applies the existing inverse-character
coefficient-set invariance. It identifies the full sets of Whittaker functions,
without fixing a functional or a coefficient vector.
`rankOneExtensionWhittakerType_iff` applies the published transport of
admissibility, finite generation over the group algebra and the entire
one-dimensional Whittaker-functional space. This transports an existing
Whittaker-type assertion; it does not establish preservation under induction.

`rankOneExtensionSymmetricLPolynomial_iff` applies
`IsPadicSymmetricLPolynomial.congr_equiv` with the identity equivalence on the
test representation. It preserves the exact polynomial and supplied additive
Haar measure. It works for either rank order and does not assume that a
certificate exists.

`rankOneExtensionUnequalRankZetaValuesAt_eq` applies the existing fixed-rank
zeta-value invariance with the same identity equivalence on the test factor.
The induced small rank is `1+(t+1)`, whose predecessor in the zeta API is
`1+t`. The test predecessor satisfies `r = (1+t)+(j+k+1)`.
Both quotient and rectangular measures are arbitrary supplied measures and
remain the same on the two sides. This identifies rational continuations
of coefficient integrals without asserting convergence or rationality.

The construction is internal: all proofs directly instantiate published
equivalence invariance. The intended later application is the original
restricted JPSS Lemma 5.5 route, but none of its compact-section, scalar
Fourier-smoothing or base-to-induced zeta comparisons is asserted here.
The module does not assume or prove L-factor multiplicativity or the later
Section 9.3 tail theorem. The parent target and its imports are unchanged.
