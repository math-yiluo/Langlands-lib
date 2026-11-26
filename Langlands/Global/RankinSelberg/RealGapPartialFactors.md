# Column products for the split real square test

This module is the real counterpart of the Library's `ComplexGapPartialFactors`.

`columnProduct n m f` is the Schwartz function `X ↦ ∏_j f_j(X_{·j})` on `n × m` real matrices built from
Schwartz functions `f_j` on `ℝⁿ`; `columnProduct_apply` evaluates it. It is constructed by induction on
`m` with the Library's `ComplexGodementColumnProduct.schwartzProd`: restriction to the preceding columns
and projection to the last column are continuous linear maps, and the operator norm of a matrix is
bounded by a constant times the sum of the norms of the two parts (`norm_le_cutLast_takeLast`).

`RealGapPartialFactorsStatement` (proved by `realGapPartialFactors`): for `a ∈ ℝˣ` and split factors
`T : GodementColumnFactors (t+1) q`, the square test `T.squareEval` and the last-column test `T.tail last`
satisfy `HasSplitPartialTest` with leading factor `T.leading`, trailing factor the column product of the
remaining tail tests, and frequency factor `columnSchwartzFourier a (T.tail last)`. The proof compares the
leading and trailing columns of the two-block coordinates with those of `squareEval` and reindexes the
trailing columns.

This is the split-test form of the partial Fourier transform in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §10.2, (10.4)–(10.5), pp. 72–73.
