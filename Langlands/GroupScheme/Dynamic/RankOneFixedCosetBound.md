# Fixed points of an actual dynamic quotient in semisimple rank at most one

This internal construction combines the published fixed-coset embedding with
the published sign embedding of the actual relative Weyl quotient. It works
over an algebraically closed field `k : Type u`, in every characteristic.

Let `G` be connected reductive, let `i : T → G` be a split maximal torus,
and assume that every pair of actual roots is integrally linearly dependent.
Choose any cocharacter `χ : Gm → T`. Let the closed subgroup inclusion
`j : P → G` represent the actual dynamic subgroup `Dynamic.parabolic (χ ≫ i)`,
and retain the explicit hypothesis `MaximalToriAreConjugate P`.
Let `q : G → Q` be flat, surjective and quasi-compact, with its fibers on
every test scheme exactly the right cosets of the subgroup represented by `j`.

`Dynamic.rankOneFlagQuotientFixedPointSignEmbedding` embeds the rational
points of `Q` fixed on every test scheme by the canonical descended action
restricted along `i` into `Bool`. The action is the existing
`Dynamic.flagQuotientSchemeAction`, so the conclusion concerns the actual
scheme action and all-test fixedness, rather than fixedness under only `T(k)`.
The accompanying theorems `finite_rankOneFlagQuotientFixedPoints` and
`card_rankOneFlagQuotientFixedPoints_le_two` give finiteness and cardinality
at most two.

The implementation supplies all the small inputs of
`torusFixedPointWeylEmbedding`. The published dynamic torus factorization
places `T` inside `P`. The whole-torus centralizer lies in the dynamic
centralizer and hence in the dynamic parabolic, giving the required
containment of rational centralizer points. Reductive smoothness makes the
source locally of finite type. The structure equation of `q` then makes `q`
locally of finite type; its surjectivity and algebraic closedness lift every
rational quotient point, with no finite-type hypothesis on `Q` required.
The published restriction and quotient-action formulas establish
equivariance. Finally the fixed-point embedding into the actual
`N(k)/Z(k)` is composed with the published rank-one quotient sign embedding.
The finite and cardinality statements follow from this injection into
`Bool`.

This is a derived helper for the positive-root uniqueness task. It retains
maximal-torus conjugacy inside the represented stabilizer; it does not prove
that geometric input, properness of `Q`, a dimension bound, or
`RankOnePositiveRootUniquenessStatement`. No regularity assumption on `χ`
or nonemptiness assumption on the roots is used.
