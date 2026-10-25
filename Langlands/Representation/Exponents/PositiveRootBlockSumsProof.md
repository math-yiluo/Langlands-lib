# Finite cancellation for weighted positive-root sums

The theorem `Langlands.Exponents.positiveRootBlockSums` proves exactly
`Langlands.Exponents.PositiveRootBlockSumsStatement`. This is a source-free
internal finite-algebra adapter for the existing weighted parameter definition.

`adjacent_sum` multiplies each adjacent-root coordinate by the positive
fine-block size. Nonzero real casts of those sizes cancel the reciprocal
factors. The resulting two indicator functions are supported at the two
actual adjacent fine-block indices. Their sums both equal the supplied
coefficient, so their difference is zero. `weighted_sum` substitutes the
given expansion, distributes the size factors, exchanges the two finite
sums, and applies this cancellation. Strict positivity of the coefficients
is retained in the hypothesis; the algebra only needs the expansion.

`middle_sum` reindexes a middle block through its refinement's actual
`indexEquiv`. The published `index_index_eq_flatten` and `blockIndex_index`
identify the fine block containing each coordinate. Each fine value occurs
exactly its block size times, so the resulting sum is `weighted_sum`.

`transport_blockIndex` eliminates a literal block-shape equality and proves
that the expanded vector is unchanged by its equality transport.
`coarse_sum` uses this fact and reindexes a coarse block through `Q`.
The actual nested-coordinate identity decomposes the result into middle
block sums, after the finite casts identifying each middle block's size.
Each such sum is zero by `middle_sum`.

The final theorem assembles the three clauses in their original order,
including rank zero and empty root sums. It asserts no branch cone,
occurrence, persistence, analytic continuation, comparison or head.
