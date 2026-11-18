# Numbered integral simple roots and coroots of type B

The numbered simple roots are the consecutive coordinate differences,
ending in the last coordinate vector. The simple coroots have the same
chain and end in twice that coordinate vector. Their pairing is exactly
Mathlib's `CartanMatrix.B` in its given order.

A common family with final multiplier `d` provides both constructions.
Prefix sums distinguish each chain generator and its final multiplier,
so a positive multiplier proves integral linear independence. Forward
coordinate differences are sums along the chain. Adding the last
generator shows that coordinate roots, doubled coordinate coroots and
positive coordinate sums lie in the appropriate additive cone. Signed
pairs of coordinates therefore lie in that cone or its negative, for
both root and coroot multipliers.

The proof reuses the published prefix-sum additive map from
`TypeDNumberedVectors`, whose definition does not depend on type D.
The remaining arguments are internal integral coordinate calculations
and induction along a finite chain. No group-scheme hypothesis, field,
characteristic restriction or new external translation is used.
