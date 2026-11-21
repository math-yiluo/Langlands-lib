# The affine column Fourier transfer in the larger-gap unfolding

For a complex Schwartz column test, partition the coordinates into two blocks and fix a frequency in the first and a physical position in the second. `complexGapColumnFourier` exchanges integration in the first block with integration of the positive Fourier transform in the second block, with the opposite character there. The statement allows an arbitrary invertible matrix multiplying the column and proves absolute integrability of both slices.

The additive change of variables moves that matrix to inverse-transpose multiplication on the Fourier side and gives one factor of the inverse normalized determinant. The partial Fourier inversion theorem supplies the equality for the pulled-back Schwartz test. The slice integrability bounds follow by comparing the coordinate norm to the norm of the full column. `complexGapColumnFourierProduct` applies the result to independent columns and combines their determinant factors by finite product integration.

This is the Fourier and determinant calculation used inside the coordinates of Lemma 10.2. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
