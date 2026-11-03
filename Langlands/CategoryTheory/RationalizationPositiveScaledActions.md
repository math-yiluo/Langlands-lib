# Positive denominators for exact scaled integral lifts

This internal algebraic adapter works in any preadditive category and for any
possibly noncommutative ring. Its input is the published
`Rationalization.ScaledIntegralLift α`, with a nonzero integer denominator `d`
and an integer-linear lift `g` of the original rational action `α` satisfying
all three exact scaled laws.

`ScaledIntegralLift.neg` replaces `(d,g)` by `(-d,-g)`. Additivity of
rationalization preserves the rational identity, and negation preserves the
scaled unit identity. In the multiplication law, the two negative factors
cancel on both sides. The output is a lift of the same action `α`.

`ScaledIntegralLift.positive` retains the original lift if `d > 0` and uses
`neg` otherwise. The original nonvanishing of `d` proves
`positive_denom_pos`. The natural number `positiveIndex` is the absolute value
of that normalized denominator. `positiveIndex_cast` identifies its integer
cast with the normalized denominator, and `positiveIndex_pos` proves it is
strictly positive. Thus consumers with positive natural torsion indices can
use the exact normalized lift directly.

The result is derived from the existing scaled-lift structure and elementary
integer sign identities. It imposes no positivity condition on the original
lift, assumes no torsion-freeness of integral Hom, and constructs no geometric
quotient or integral ring action.
