# Universal testing and normalization of groupoid cocycles

Author: Worker 148.

This internal algebraic unit imports the published cobar definitions and the
universal points of `RingEtaleEquivalenceRelation`. Rings B and C belong to an
arbitrary universe u; the module M may belong to an independent universe v.

`IsUniversalOneCocycle` is the single equation at the universal composable
point. `isOneCocycle_iff_universal` identifies the existing flat-test
`GroupoidCoaction.IsOneCocycle` predicate with the cocycle equation in the
universal ring of composable points. The forward implication uses the published
flatness of that ring. For the reverse implication, the universal equation is
mapped along `composableLift`; naturality of tensor pullback and
`coactionCompose` identifies its image with the equation at the given points.

`IsOneCocycle.specialize` proves the equation at any ring-valued composable
points, without a flatness assumption on the test algebra. Its proof is the same
specialization of the universal equation.

`IsOneCocycle.identity_eq_zero` proves that a cocycle restricts to zero at the
identity. At the identity the composite map equals tensor pullback, by the
counit identity and tensor induction. The cocycle equation then reads
y = y + y, hence y = 0.

These results are derived directly from the published formulas and universal
point constructions. They do not establish geometric vanishing, affine descent,
or the main acyclicity theorem.
