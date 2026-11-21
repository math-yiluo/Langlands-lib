# Fourier exchange inside the split Godement kernel

`complexGapTailExchange` proves the inner passage from the ordinary to the alternate expression for the split Godement kernel. The leading block, first tail column, final frequency, smaller-group arguments and determinant character are included. Both fiber integrals converge absolutely, and each exchanged column contributes an inverse normalized determinant to the scale factor.

For fixed outer data, the later rectangle and the upper unipotent tail act through `packedTail`. They fix the leading columns, the first tail column and the last row of the inverse. The determinant is unchanged. Conjugating the inverse upper block by the leading group element changes the rectangle and leaves its first column zero. The Whittaker character of this conjugated inverse is the standard character of the tail at `a`, since the smaller vector transforms at `-a`. This gives the phase for the triangular Fourier theorem. On the alternate side the earlier tail positions are evaluated at the inverse transpose of the remaining matrix with just the tail block present.

This is the fixed outer data identity for (10.4) and (10.5). [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`alternateKernel_eq` identifies the alternate tail kernel with the fixed factor times the triangular Fourier kernel.
