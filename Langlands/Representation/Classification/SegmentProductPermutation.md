# Permuting segment-product data

Author: Worker 17.

This internal construction reindexes the existing `SegmentProductDatum`. It is
derived directly from the definitions in `Classification.LanglandsData`,
`Classification.Segments` and `Group.GL.AdjacentMergeShape`, with no new
literature assertion.

`SegmentProductDatum.permute d σ` puts the original segment and actual smooth
representation with label `σ i` at new position `i`. The sum of the degrees is
unchanged by `Equiv.sum_comp`. The construction keeps the ambient rank, field,
topological data and independent carrier universe parameters. It applies to
empty as well as nonempty data.

The projection lemmas identify the length, segments, blocks and block shape.
The identity permutation gives the original datum. Performing `σ` and then
`τ` gives `τ.trans σ`, which acts by `i ↦ σ (τ i)`. The induced representation
is definitionally the normalized induction of that permuted family; this
equality makes no claim of an isomorphism to the original induced product.
Segment heads are retained by applying the original head assertion at `σ i`.

`permute_occurrences` uses `σ.symm` to locate each original occurrence. The
equation `σ (σ.symm i) = i` supplies the dependent equality of ranks and the
identity isomorphism after transporting the original block. Thus repeated
segments and blocks remain separately indexed.

`IsPrecedenceOrdered.permute_adjacentSwap` assumes the original precedence
ordering and that the adjacent segments at positions `j` and `j+1` are
unlinked. An adjacent transposition preserves the order of each ordered pair
of positions except that pair itself; the finite index comparisons are checked
by arithmetic case analysis. The exceptional pair cannot precede in the new
direction because precedence implies linkage and linkage is symmetric. The
other pairs use the original precedence ordering.

No square-integrability, exponent comparison, or isomorphism between different
orders of normalized induction is established here. Those are separate inputs
to the ordered-segment conversion.
