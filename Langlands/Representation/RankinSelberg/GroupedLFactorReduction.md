# Common real twists in the tempered block product formula

Author: Worker 1748.

This internal reduction adapts the existing `TemperedLFactorStatement` to the
equal-exponent groups in the JPSS 9.5 proof. It retains that analytic statement
as an explicit premise.

`IsPadicRankLPolynomial.congr_equiv` is reused from `SegmentPairPoleOrder`;
it transports actual representation equivalences at arbitrary ranks by
splitting the zero and successor cases.
`realTwistPolynomial` is the ring homomorphism given by substitution
`X ↦ q^(-s) X`. `realTwistCharacter` is the smooth real unramified character
of the multiplicative group. Its complex-power formula follows from
`Complex.ofReal_cpow`.

`IsPadicRankLPolynomial.twist_real` applies the published closed
`unramifiedTwistLFactor` first to the left representation and then to the
right one. The two polynomial substitutions are retained in that order,
without needing an identity between complex powers.

`TemperedLFactorStatement.blockShape` writes each positive block size as a
successor and applies its explicit premise. `commonRealTwists` applies the
preceding two-variable twist formula both to the induced pair and to every
block pair. `normalizedProductDeterminantTwistEquiv` identifies the twists
of the actual inductions with induction of the twisted factors. Polynomial
substitution preserves the two finite products because it is a ring
homomorphism.

All content is internally derived from the imported Library results. This
module does not supply a closed proof of Proposition (8.4), grouping, or
Theorem (9.5).
