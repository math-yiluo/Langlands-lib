# Proof of the separated torus normalizer statement

`Langlands.GroupScheme.separatedTorusNormalizer` proves
[`SeparatedTorusNormalizerStatement`](SeparatedNormalizerStatement.md) in
every universe. Take a scheme `S`, a group scheme `G` over `S` with smooth,
separated, quasi-compact structure morphism, a commutative group scheme `T`
that is a relative torus, and a closed subgroup embedding `t : T.toGrp ⟶ G`.
The proof returns a group scheme `N` with smooth structure morphism and a
closed subgroup embedding `n : N ⟶ G` that represents the all-test
normalizer functor `torusNormalizer t`.

## The Lean proof

The proof applies
`relativeTorusSmoothNormalizerModel_of_squareZeroCohomology` from
[`TorusNormalizerInfinitesimalLifting`](TorusNormalizerInfinitesimalLifting.md).
That construction needs only smoothness of `G` over `S` and an explicit proof
of `HomScheme.SquareZeroHomomorphismCohomologyStatement`. The proof supplies
the Library theorem `HomScheme.squareZeroHomomorphismCohomology` from
`Langlands.GroupScheme.HomScheme.SquareZeroCohomology`. The construction
returns a closed representative of `torusNormalizer t` together with a
proof that its structure morphism is smooth. The representative's group and
inclusion give `N` and `n`. Its closedness field, the smoothness proof and
its representation field give the three conjuncts of the conclusion.

In outline, the closed representative is the locally finitely presented
closed normalizer from
[`MultiplicativeTypeNormalizerFinitePresentation`](MultiplicativeTypeNormalizerFinitePresentation.md).
Its smoothness follows from the square-zero lifting criterion and étale
descent along a splitting cover of the torus.

The separatedness and quasi-compactness hypotheses of the statement are not
used. The proof uses no source beyond the cited Library results, and no
step relies on the ambient group being affine over the base.
