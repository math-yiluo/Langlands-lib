# Algebraic criteria for bounded powers

Author: Worker 56.

The predicate imported from `PowerBoundsDefinitions`, `HasBoundedPowers a`,
means that one positive real constant bounds the norm of
every power, including the zeroth power. Nilpotents satisfy this condition
because only finitely many powers can be nonzero. Bounded unital ring maps
preserve it. Every bounded multiplicative seminorm takes value at most one on
such an element: a value greater than one would have unbounded powers.

The main algebraic lemma treats a nontrivial commutative coefficient ring whose entire
image in an ultrametric normed algebra is bounded. The span of finitely many
vectors over that image has a common bound, by the strong triangle inequality.
An element integral over the coefficient ring has all its powers in the span
of the powers below the degree of its minimal polynomial. Mathlib proves this
span assertion by division by a monic annihilating polynomial. Combining these
facts gives a bound for every power. The target algebra may be the zero ring.
The proof uses no completeness, valuation nontriviality, or Noetherianity.
The preceding finite-span norm estimate does not require the coefficient
ring to be nontrivial.

An explicit-relation version accepts a ring map and a monic annihilating
polynomial. The final specialization constructs the norm unit ball as an
actual subring and lifts any monic polynomial whose coefficients have norm at
most one to that subring. It then applies the preceding result. Its unit-ball
specialization assumes a norm-one, nontrivial ring; the more general
bounded-image result has no norm-one premise.

This implements the final algebraic step of Proposition 2.6.5, page 12,
of the retained notes of Vladimir Berkovich's course. The norm-controlled
monic relation for general affinoids is constructed separately in
`SpectralPowerBoundProof`, using normalization and minimal-polynomial
coefficient bounds. The source is undated and its note-taker is unidentified.
Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`;
content SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
Retained file:
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The source bounds positive powers; including the zeroth power only enlarges
the constant. The implementation uses that equivalent convention explicitly.

The spectrum dependency is `Spectrum.Definitions`. Mathlib
`IsIntegral.mem_span_pow` supplies the finite span; the finite-sum norm estimate
is proved here.
