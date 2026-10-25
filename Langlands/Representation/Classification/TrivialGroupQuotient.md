# Scalar-line quotients for a trivial group

Author: Worker 391.

`Langlands.Classification.scalarLineIntertwiningMap` constructs an actual
intertwining map between two complex representations of a trivial group.
Its inputs are a linear equivalence from the source carrier to `ℂ` and a
vector `v` in the target. Its underlying linear map sends `x` to `e x • v`.
It needs no irreducibility assumption. Every group element is the identity,
so this map intertwines the actions.

`Langlands.Classification.isIrreducibleQuotient_of_subsingleton_linearEquiv`
is an internal algebraic support lemma for the rank-zero case of ordered
special-segment quotient coverage. It concerns an arbitrary trivial group,
a complex representation whose carrier is linearly equivalent to `ℂ`, and
an arbitrary irreducible complex target representation. The common carrier
universe is independent of the group universe. The conclusion is the published actual
irreducible quotient relation, including a surjective intertwining map.

Irreducibility makes the target nonzero, so choose a nonzero vector `v`.
Apply `scalarLineIntertwiningMap` to this vector. The inverse image of `1`
maps to `v`, making the intertwiner nonzero. Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` then makes it surjective.

This is a direct derivation from the published constituent relation and
Mathlib's irreducibility algebra; no external classification result is used.
It constructs neither the rank-zero induced scalar-line equivalence nor a
segment datum. Those are separate inputs to its intended specialization.
This contribution does not prove positive-rank coverage or the full
`OrderedMultisegmentQuotientExhaustion` target.
