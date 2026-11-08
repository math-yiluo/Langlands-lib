# Proof of actual relative-root rank-one factorization

`rootRankOneFactorization` proves the published proposition
`RootRankOneFactorizationStatement.{u}` exactly, at arbitrary universe `u`.
Fix any field `k`, connected reductive `G` over `k` and actual maximal split
torus `i : T.toGrp → G`. For every relative root `a` and nonidentity rational
`u` in `RelativeRoot.subgroup i a`, the theorem gives the following. There is a
unique opposite factor pair `(u′, u′′)` with `m = u′ * u * u′′` normalizing `i`.
Both factors are nontrivial, and the class of `m` is a relative reflection for
`a`. If `2 • a` is not a relative root, then `u′ = u′′`, `u′ = m⁻¹ * u * m` and
`m * m` lies in the torus image. This is the content of Kaletha–Prasad 2.11.17
and Conrad–Gabber–Prasad C.2.24(i),(iii) as specialized in the statement.

## Implemented proof

The proof applies `rootRankOneFactorization_of_componentReductivity` (module
`Rational.RankOneParabolicCovering`) to the published unconditional theorem
`RelativeRoot.kernelCentralizerComponentReductive`. That theorem proves that the
identity component of every full-kernel centralizer is connected reductive.

The applied implication works inside that identity component. A descended
rank-one parabolic double-coset covering, obtained from the proper flag quotient
and its orbit limits, supplies opposite factor pairs there. They are transported
back to `G`. The published `hasRankOneFactorization_of_hasOppositeFactorPairs`
then derives uniqueness, nontriviality, the reflection property and the
nonmultipliable consequences.

No general rational Bruhat decomposition, Tits system or standard-parabolic
classification is used. No hypothesis is added to the statement.
