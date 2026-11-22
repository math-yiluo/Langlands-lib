# Haar integration in the triangular split chart

`continuous_packedTail` gives continuity of the matrix with the
upper rectangle and upper-unipotent tail in the consecutive blocks.

`complexGapTriangularChart` gives Haar measure on `GL_(k+q+1)(ℂ)` as a positive constant times the image of a product measure. The outer variables are the leading `GL_k` matrix, the logarithmic tail diagonal, the compact unitary factor and the first rectangular column. The inner variables are the remaining `k × q` rectangle and the unipotent tail of size `q + 1`. The tail diagonal carries the product of the root modulus and the inverse determinant power from the consecutive-block chart.

The proof inserts the tail Haar formula into the consecutive-block right chart and moves the determinant weight onto the tail diagonal. Right invariance of compact Haar absorbs the embedded tail unitary factor, with the tail measure normalized to have mass one. The rectangle shear then separates the first column from the remaining columns and preserves their additive product measure. The block product identity identifies the composite with `triangularRightChart`, in which the remaining rectangle and upper unipotent tail multiply the retained matrix before the leading group factor. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, pp. 72–73](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
