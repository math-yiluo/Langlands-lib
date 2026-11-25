# Unlinked exchanges involving one zero induction weight

This module treats pairs of real induction blocks with exactly
one zero weight. It composes the published character-induced or induced-character
unlinked swaps after expanding the zero-weight block into its sign and unsigned
characters. Outside the scope stated here it does not prove
`RealInducedInducedFiltrationStatement`; the Library proves that statement as
`realInducedInducedFiltration` in `RealInducedInducedFiltrationProof`.

`injective_zero_left` and `injective_zero_right` work in arbitrary surrounding
lists `pre`, `post` of total rank `n`. They retain descending real exponent order,
unlinkedness of the two original blocks, and the condition that one weight is
zero and the other nonzero. Each proof applies two mixed swaps, transports
unlinkedness through `areRealBlocksUnlinked_of_mem_expand`, composes the
injective intertwiners, and returns to the original standard modules using
`realStandardModule_append_expand` and `RealInjectiveIntertwinerExists.of_eq`.

`exists_bijective_intertwiner` specializes these actual injective maps to GL4.
It converts standard equivariance to equivariance modulo the zero subspace.
The published `RealInducedPairKTypeTransport.surjective_of_injective` then gives
surjectivity, hence a bijective exact intertwiner from `[induced d, induced e]`
to `[induced e, induced d]` in descending exponent order.

`filtration` reverses the inputs to that exchange. For an ascending pair
`d,e`, with exactly one zero weight and
`AreRealBlocksUnlinked (induced e) (induced d)`, it maps the identity filtration
of `[induced e, induced d]` along the surjective exact map. This supplies the
one-piece actual adjacent filtration of `[induced d, induced e]`.
`RealInducedPairSingleZeroUnlinkedFiltrationStatement` records precisely these
hypotheses and conclusion; `realInducedPairSingleZeroUnlinkedFiltration` proves it.

The provenance is entirely internal: the zero-weight expansion, the two proved
mixed unlinked swaps, equality transport, compact type counting, and the
filtration calculus. No external source, classification result, supplied
operator, occurrence assumption, or unproved GL3 filtration is used. The
both-zero case is already covered by `RealInducedPairWeightZero.both_zero`.
