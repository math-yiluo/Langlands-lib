# Cocharacter weight sums and character-pairing regions

For an affine group scheme locally of finite type over a field, a split torus
mapping to that group, and any cocharacter of the torus, the cocharacter weight
space of integer weight `m` equals the sum of the torus character weight spaces
whose integral pairing with the cocharacter equals `m`. All coefficient
extensions in the existing weight spaces are retained. There is no genericity,
smoothness, connectedness, reductivity, or maximality hypothesis.

This is an internal consequence of the existing split-torus adjoint weight
decomposition and restriction of weight spaces in `Torus.WeightDecomposition`
and `Rational.GenericLieWeights`. The Lean proof projects onto a weight space
for the restricted action. Every vector is a sum of torus weight vectors, and
the projection fixes those restricting to the selected weight and kills all
others. Finally `gmEndEquiv` identifies the restricted character with the
integer given by `latticePairing`.

`RelativeRoot.adjointSemigroupWeightSpan i A` is the sum of the existing adjoint
weight spaces indexed by the characters in a subsemigroup `A`. Its definition
requires only that the target group be affine; the acting commutative group
need not be a torus. The published theorem `actionWeightSpace_conjugation`
identifies the intrinsic `semigroupWeightSpan` for conjugation with this adjoint
span, as expressed by `semigroupWeightSpan_conjugation`.

For a split torus and a target locally of finite type, the remaining lemmas
identify `semigroupWeightSpan` on `nonnegativeSemigroup`, `zeroSemigroup`, and
`positiveSemigroup` with, respectively, the sum of cocharacter weights indexed
by natural numbers, the weight-zero space, and the sum of weights `n + 1` for
natural numbers `n`. These are the exact sums in `DynamicLieStatement`.

The first and third comparisons identify nonnegative and strictly positive
integers with their natural-number indices. The zero comparison is the weight
fiber formula at zero. Thus these lemmas include the zero cocharacter and
cocharacters on any weight hyperplane. They reuse the published action-weight
comparison and do not assert the Dynamic Lie theorem or semigroup realization.
