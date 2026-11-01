# Chamber restriction and diagonal real-part projection

Worker 526 derives these coordinate lemmas from the actual chamber labels in
`IntersectionChamberCoordinates` and the real-part fibre formula and block-sum
algebra in `MaximalConeExponents`. Worker 828 supplied the chamber coordinates
and their constancy on each fine block. This is internal finite-sum algebra;
it makes no new assertion about an external literature source.

The namespace is `Langlands.Geometric.ChamberProjection`.
`diagonal_sum_eq_fibre_sum` takes arbitrary block shapes `D`, `C`, a
permutation `w` and labels `q` satisfying
`q (blockIndex D a) = blockIndex C (w a)`. Fine scalar coordinates `x k`
give the repeated diagonal values `x k / D.size k`. Their sum over the
inverse image of target block `j` is the sum of `x k` on its labelled
fine blocks. The proof rewrites the target block sum as a filtered sum
over all coordinates, reindexes by `w`, applies `sum_blockIndex`, and
cancels the positive fine block sizes. Its private block-sum lemma uses
the actual block-coordinate equivalence.

`chamberRestriction_isRealPartOf` applies `T.isRealPartOf_coarsen` to
`chamberIndex`. Its real-part clause requires no monotonicity of the labels.
Restricting a fine character along the chamber tuple map therefore sums
its real coordinates on the label fibres.

`diagonal_projection_of_character_extension` takes actual characters
`psi`, `chi`, real parts `x`, `y`, and
`psi.comp chamberRestriction = chi`. Real-part uniqueness identifies
`y` with those fibre sums. The actual source-intersection Levi equality
supplies `chamberIndex_blockIndex`, so the first lemma identifies each
`y j` with the inverse-permuted diagonal block sum.

These results retain arbitrary ranks, rank-zero empty sums and positive
fine sizes. They assume neither minimality nor representation-theoretic
occurrence, and they do not construct a character extension. The actual
extraction and source untwisting are in `GeometricPieceUntwistedProjection`.
