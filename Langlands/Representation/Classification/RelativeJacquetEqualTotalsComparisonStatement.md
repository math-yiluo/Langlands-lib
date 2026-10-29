# Constituent comparison from equal actual Jacquet totals

`Langlands.GLRelativeJacquetEqualTotalsComparisonStatement` isolates the algebraic
equal-sums step in the relative Jacquet comparison. It is a proposition
definition, with independent universes `uF`, `uV`, `uW` and `uX` for the local
field, coarse input, refined constituent and selected coarse constituent.

For every positive rank, ordered block shape `B` and actual refinement `S`,
let `A` be a smooth complex representation of `B.Levi F.Carrier`. The hypotheses
give an actual finite composition series `s` of `A`, with every original graded
quotient admissible. They also give a refined representation `τ`, a natural
number `N`, and actual finite composition-series multiplicities of `τ` in
`innerJacquet T B S A` and `ambientJacquet T B S A`, both equal to `N`.
The length of `s` is allowed to be zero.

For every irreducible admissible coarse representation `μ` presented as an
actual subquotient of `A`, the conclusion supplies a natural number `m` and
actual finite composition series recording multiplicity `m` in both
`innerJacquet T B S μ` and `ambientJacquet T B S μ`. The subquotient witness is
an invariant subspace `U` of `A` and a surjective intertwiner `U → μ`.
It allows the carriers of `A` and `μ` to lie in different universes.

All Jacquet modules are the existing normalized opposite constructions on
their actual coinvariants. The ambient construction first takes actual
normalized outer induction, with right translation and positive upper
half-modulus covariance, and then composed opposite Jacquet. No normalization
or representation is replaced by an abstract certificate.

## Derived provenance and proof dependencies

This internal bridge is derived from existing Library interfaces. It is not
claimed as a literal statement from an external source. The published
`glRelativeJacquetFiltrationMultiplicity` decomposes each supplied total over
the original grades of `s`. The published `glRelativeJacquetEmbedding` bounds
each inner grade count by its ambient grade count, using irreducibility and
admissibility. `HasJordanHolderMultiplicity.unique` identifies the inner count
with the supplied summand. Equal finite sums of these natural numbers then
force equality at every grade.

The published `simpleSubquotientFactor` locates `μ` among the grades of the
supplied series after passing from its surjective presentation to its actual
kernel quotient. Actual representation equivalences and finite-series
multiplicity transport then transfer the two grade counts to `μ`.

The supplied composition series, admissibility of its grades, and equal
actual totals are hypotheses of this algebraic bridge. Their construction for
the generic fine induction remains a separate obligation. This statement does
not assert positivity, the quotient criterion, generic Weyl counts, a Hom-rank
comparison or an irreducible head. In particular, it is not an unconditional
proof of `GLRelativeGenericComparisonStatement`.
