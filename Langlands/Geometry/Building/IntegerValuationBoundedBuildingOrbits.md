# Bounded building orbits from common apartments

This internal derived unit works on the original integer-valued quotient.
Common apartments, a bounded basepoint sharp fixer, and a metric making the
original rational-point action isometric are explicit premises.

Common apartments factor each group element as `p * n * q`, where `p` and `q`
belong to the same basepoint sharp fixer and `n` belongs to the actual
normalizer. For an algebraically bounded set `X`, the required normalizer
elements lie in `P * X * P`, which is algebraically bounded. Their apartment
orbit is finite by the finite normalizer-orbit theorem. Its image in the
quotient is therefore metrically bounded. Since `p` and `q` fix the basepoint
and the action is isometric, the displacement of `p * n * q` at that point is
the displacement of `n`. This bounds the entire orbit of `X`.

The published bounded-action comparison then bounds the orbit at every
quotient point. If the supplied metric is also complete and nonpositively
curved in the KP midpoint sense, the published
`Metric.KP.boundedActionFixedPoint` gives a common fixed point of every
algebraically bounded subgroup. The proof applies that theorem to the
restriction of the original action to the subgroup; it requires no topology
on the group.

`IntegerValuation.BoundedFixedPointFromCommonApartmentsStatement` states this
conditional fixed-point conclusion for all compatible integer-valued fields,
all supplied integer-valued building data, and all supplied complete NPC
isometric metrics, at arbitrary universe `u`.
`IntegerValuation.boundedFixedPointFromCommonApartments` proves it. A bound on
the sharp fixer of one chosen apartment point suffices.

The metric, common-apartment existence and boundedness of the sharp fixer are
not constructed by this argument. No local compactness premise or local-field
instance on the maximal unramified extension is used.
