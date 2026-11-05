# Actual commuting torus and additive factorization data

`TorusAdditivePowerFactorizationData G x` records a positive natural exponent,
an actual commutative torus with a closed inclusion into `G`, an actual rational
torus point, and an actual homomorphism from the additive group into `G`. Its
equality factors the given positive power of `x` as the torus point's image
times the additive homomorphism evaluated at coordinate one. It also records
that those two rational factors commute. `VectorGroup.coordinateOnePoint` is
only an abbreviation of the explicit coordinate-one point in the existing
`PositivePowerTorusAdditiveFactorizationStatement`.

This is internal derived data for assembling that statement. The small lemmas
`rationalPoints.map_comp_apply` and `map_zero_apply` express postcomposition and
the identity value of the zero group homomorphism in the existing actual-point
convention.

`ConnectedCommutativePowerEnvelope.factorizationOfPointFactors` transports an
exact torus/additive factorization of the envelope's chosen point to the
ambient group. It composes both homomorphisms with the envelope inclusion,
composes the closed immersions, and applies the induced homomorphism on
rational points to the given factorization. The exponent remains the envelope's
positive exponent. The factors commute inside the commutative envelope, and
that equality is preserved by the homomorphism on rational points.

`positiveCharacteristicFactorizationData` works for every affine locally finite
type group scheme over a field of prime characteristic `p`, including imperfect
fields, with no ambient smoothness assumption. It takes the connected
commutative power envelope and applies `positiveCharacteristicTorusPower` to
its point. If the envelope exponent is `m` and the further exponent is `p ^ r`,
the returned exponent is `m * p ^ r`, which is positive. The torus inclusion is
the composite closed immersion. The additive homomorphism is zero, whose value
at coordinate one is the identity, so the torus point equation gives the
required factorization and the factors commute.

These are adapters of the two imported envelope constructions and the
positive-characteristic torus-power construction. They add no structural
hypotheses or independent source assertions and do not yet supply the
characteristic-zero factorization inside a connected commutative group.

Rational-point functoriality reuses the published
`Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply`.
