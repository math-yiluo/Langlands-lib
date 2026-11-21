# Product measure on the triangular column coordinates

In Lemma 10.2, the columns after the first tail column have free entries above their pivots. These entries run over the leading rectangle and the strict upper triangle of the tail. On the Fourier side the free entries start one row below the preceding pivot. They run over the strict upper triangle of the tail with its indices transposed.

`prefixIndex` and `suffixIndex` implement the two finite reindexings. `complexGapColumnCoordinates` proves that the induced equivalences preserve measure. The proof unfolds the rectangular measure and entry Haar measure as products of the same additive self-dual measure, then uses the finite product formula for boxes to group entries by column. The cardinalities allow an empty rectangle or an empty strict upper triangle.

This coordinate lemma identifies the measures in the direct and Fourier-side domains of the triangular exchange. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
