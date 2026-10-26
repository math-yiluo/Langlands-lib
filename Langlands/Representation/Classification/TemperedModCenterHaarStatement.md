# Haar normalization invariance of temperedness modulo the center

Author: Worker 573.

`Langlands.TemperedModCenterHaarInvariantStatement` asserts that
`IsTemperedModCenter ρ μ` and `IsTemperedModCenter ρ ν` are equivalent for
two Haar measures on the actual quotient `G ⧸ Subgroup.center G`.
The group is a topological group, and this quotient is assumed locally
compact and second countable. Both measures use one supplied measurable
space, required to be the Borel sigma algebra of the quotient topology.
The group and complex representation carrier lie in independent universes.
There is no irreducibility, finite dimension, nonzero-carrier or positive-form
hypothesis.

The analytic predicate retains its published meaning: admissibility and one
unitary central character for which every absolute smooth-dual coefficient
belongs to `L^(2 + ε)` for every positive real `ε`. The statement compares this
predicate for the two measures without changing the representation, the
actual quotient or its measurable space.

This is an internal consequence of the published
`Langlands.HaarMemLpInvariantStatement`, rather than a claim quoted from the
representation-theory literature. The intended deduction keeps admissibility
and the same unitary central-character witness, and transfers every real
coefficient norm at exponent `ENNReal.ofReal (2 + ε)` using
`Langlands.haarMemLpInvariant`. That proof uses Haar uniqueness and finite
measure scaling. This module states the consequence; it supplies no proof.

The quotient topological hypotheses remain explicit. Applications to actual
p-adic GL groups or product Levi groups must establish them independently.
Changing the Borel realization or obtaining a canonical all-Haar predicate
requires a separate adapter. No parabolic-induction, Jacquet-exponent,
tensor-comparison or classification result is asserted here.
