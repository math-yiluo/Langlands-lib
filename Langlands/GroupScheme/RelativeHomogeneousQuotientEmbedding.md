# Retaining the ambient embedding of a relative homogeneous quotient

`RelativeHomogeneousQuotient.EmbeddedHomogeneousQuotient i Y r` stores an
actual `HomogeneousQuotient i`, a morphism from its scheme to `Y`, the
factorization of `r` through its quotient projection, and monicity of the
underlying scheme map into `Y`.

`RelativeHomogeneousQuotient.quotientEmbeddingOfMapKernel` constructs this
data over every base scheme `S`. Its hypotheses are a smooth affine group
scheme `G`, a smooth closed subgroup `i : H ⟶ G`, a separated scheme `Y`
over `S`, and an actual morphism `r : G.X ⟶ Y` whose fibres on every test
scheme are exactly the right cosets of `H`. These are explicit hypotheses;
no ambient map is derived from parabolicity or self-normalization here.

The construction uses the published smooth relation associated to right
multiplication on `G` by `H`. The exact-coset condition identifies that
relation with the fibres of `r`. The published `schemeQuotientOfMapKernel`
then provides a scheme, a smooth surjective projection and a monomorphic
map into `Y`, with the required factorization. Composing the latter map
with the separated structure map of `Y` proves that the quotient is
separated. Local finite presentation descends along the smooth surjective
projection from the smooth group `G`.

For each compact open subset of `S`, its preimage in `G` is compact because
`G` is affine over `S`. The continuous image of this preimage under the
surjective projection is the corresponding preimage in the quotient. This
proves quasi-compactness of the quotient structure map over arbitrary
bases. Quasi-compactness of the projection follows from quasi-compactness
of its composite with the separated quotient structure map. The relation
comparison supplies the exact-coset condition on every test scheme.

This is an internal refinement of `RelativeHomogeneousQuotient` and the
published `HomogeneousQuotientFromEmbedding` construction, with the actual
embedding data retained for use in a relative properness criterion. Its
proof repeats the relative compact-open argument and retains the original
`SchemeQuotientEmbedding` factorization; forgetting the embedding gives
the same existence content as the conditional relative constructor.
No original-literature assertion is introduced. Properness of the
quotient and existence of an ambient map remain separate obligations.
