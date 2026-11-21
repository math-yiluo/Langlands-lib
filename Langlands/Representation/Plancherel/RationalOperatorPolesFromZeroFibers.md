# Whole-operator pole support from the zeros of cleared numerators

Take a rational family on a nonempty open subset of the actual complex
unramified character group. Suppose a regular scalar with a unitary pole
factorization controls the zeros of the cleared numerators. For every
continuation of the family, the hypothesis requires its numerator to
vanish wherever its denominator is zero and the controlling scalar is
nonzero.

Choose a denominator minimal for strict divisibility. If one of its
prime factors has a unitary zero, multiply each scalar linear test of
its numerator by the controlling scalar. This product vanishes on the
entire complex zero locus of the prime. Hypersurface divisibility gives
divisibility of the product by the prime. If the prime is absent from
the controlling scalar, it divides each unscaled test. The
whole-operator division theorem then divides the numerator and
denominator by this same prime, contradicting minimality.

In the resulting existence witness, each prime factor with a unitary
zero divides the controlling scalar and is associated with one of its
unit-circle basis roots. The other prime factors and the unit relating
their product to the denominator supply the remainder, which is
nonvanishing on all unitary characters. Polynomial uniqueness gives
the cross identity with the supplied original numerator and denominator.

This proves existence of a `RationalOperatorPolePresentation`. The
definition chooses an inhabitant of that type, with a global polynomial
numerator, a unitary pole factorization, and the cross identity.

This derived algebraic construction is for the pole support step in
Waldspurger (2003), IV.1(13) and V.3.1, printed pp. 283 and 295. Its
zero-fiber hypothesis is suited to the uniqueness of the normalized
integral operator on the `PQ`-regular locus. The separate norm estimate
for the full tensor is used in the subsequent cancellation of its
unitary poles.
