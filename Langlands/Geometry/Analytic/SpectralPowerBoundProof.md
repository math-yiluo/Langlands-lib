# Bounded powers from spectral inequalities for all presented strict affinoids

Author: Worker 56.

The closing theorem `spectralPowerBound` has the complete type
`SpectralPowerBoundStatement K`: for every actual quotient of a
finite-variable strict Tate algebra by a closed ideal, an element has
uniformly bounded nonnegative integral powers if every bounded
multiplicative seminorm takes it to at most one. The coefficient field
is complete and ultrametric. Neither a nontrivial valuation nor
reducedness, a domain hypothesis, or a nonzero quotient is imposed.

For a trivially valued field, the existing quotient-norm argument shows
that every quotient element, and hence every power, has norm at most one.
Otherwise the proof uses the actual prime quotients of the given
affinoid algebra. Their ideals are closed by the proved Noetherian
Banach theorem. The prime-quotient relation theorem constructs, for
each minimal prime, a monic polynomial over the original Tate algebra
whose coefficients have norm at most one and whose evaluation lies
in that prime.

Noetherianity gives finitely many minimal primes. The product of their
polynomials is monic, and its evaluation lies in the intersection of
all minimal primes. That intersection is the nilradical, so some power
of the evaluation is zero. Raising the product polynomial to that
power produces an actual monic relation at the original element.
Polynomial lifting through the norm-unit-ball subring proves that
products and powers retain all coefficient bounds. This step retains
nilpotents rather than imposing reducedness. The argument also permits
an empty set of minimal primes, as occurs for the zero quotient.

Finally the previously proved finite-span criterion for a monic
relation over a bounded coefficient image bounds every power of the
element. Its coefficient map is the genuine bounded presentation map
from the original Tate algebra. No normalization map, bounded lift,
monic relation, spectral-radius identity, or boundedness conclusion
is supplied as an assumption.

The additional equivalence combines this implication with the earlier
general fact that bounded powers force all spectral values to be at
most one.

The source is Proposition 2.6.4, pages 11–12, and Proposition 2.6.5,
page 12, of the retained Berkovich-course notes. The product over
minimal primes and the nilpotent power follow the source's arbitrary
algebra case. The Lean statement uses pointwise inequalities on the
actual multiplicative spectrum instead of an independently named
spectral-radius supremum. It bounds powers beginning at exponent zero;
including this extra finite term gives an equivalent boundedness condition.
The full spectral-radius identity and the maximum-modulus principle are
outside this statement. The earlier construction modules supply actual Weierstrass
division, normalization, closedness and the normed field used for the
minimal-polynomial comparison.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
