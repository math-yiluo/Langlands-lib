# Approximation by normalized orthogonal polynomial kernels

`orthogonalNormalizedPeaks` proves `OrthogonalNormalizedPeaksStatement` for
positive rank and a left- and inversion-invariant Borel probability measure on
`O(n)`. At every positive integer scale `t` it supplies a polynomial kernel of
entry degree at most `t^4`. Left convolution by the kernel equals the integral
of right translations with that kernel as weight. On a profile with Lipschitz
constant `L` in the operator matrix norm, the convolution error in supremum
norm is at most `C L / t`.

The kernel is the Haar-normalized `t^4`-th power of the positive affine trace
peak. Cyclicity of trace and the identity between inversion and transposition
on `O(n)` give the change of variables between the two formulas. The row sum of
entry norms is bounded by `n` times the Frobenius norm. By compactness, left
multiplication by an orthogonal matrix has a uniform matrix norm bound. After
subtracting the original profile under the integral, these inequalities and the
Lipschitz constant bound its norm by the normalized first moment from
`orthogonalPolynomialPeakMoment`.
