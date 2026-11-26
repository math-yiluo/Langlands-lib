# Product measure on the real triangular column coordinates

This module is the real counterpart of the Library's `ComplexGapColumnCoordinates`; its
declarations lie in the namespace `Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier`.

Let the ambient column have `k + q + 1` entries. `beforePivot k q j i` says that the row `i` lies
before the pivot `k + j + 1` of the column `j : Fin q`. In Lemma 10.2 the columns after the first tail
column have free entries above their pivots; these run over the leading `k × q` rectangle and the
strict upper triangle of the unipotent tail of size `q + 1`. On the Fourier side the free entries
start one row below the preceding pivot and run over the strict upper triangle with transposed
indices.

`prefixIndex` and `suffixIndex` are the two finite reindexings, and `prefixColumns`,
`suffixColumns` the induced measurable equivalences
`Mat_{k×q}(ℝ) × N_{q+1}(ℝ) ≃ ∏_j (P j → ℝ)` and `N_{q+1}(ℝ) ≃ ∏_j (S j → ℝ)`, where `P j` and `S j` are
the rows before and from the pivot of column `j`.

`RealGapColumnCoordinatesStatement` (proved by `realGapColumnCoordinates`): for every `a : ℝˣ`,
with `μ = realSelfDualMeasure a`, `prefixColumns` carries the product of the rectangular measure and
the entry Haar measure `RealJacquetUnipotentMeasure.entryHaar μ (q + 1)` to the product of the
self-dual product measures `piMeasure (P j) a`, and `suffixColumns` carries the entry Haar measure to
the product of the `piMeasure (S j) a`.

The proof writes the rectangular measure and the entry Haar measure as products of the same scalar
measure and regroups the entries by column, using the measure-preserving uncurrying, sum and
reindexing equivalences of finite products. Empty rectangles and empty triangles are allowed.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
