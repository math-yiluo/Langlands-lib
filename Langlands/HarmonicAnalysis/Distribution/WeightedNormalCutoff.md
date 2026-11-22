# Weighted derivative estimates for the normal cutoff

Let \(E\) and \(N\) be real normed spaces with \(N\) finite-dimensional.
The real-valued smooth test on \(E\times N\) has compact support and is flat
through order \(d+m\) on \(E\times\{0\}\). The operation `normalCutoffTest`
multiplies the test at \((x,y)\) by the fixed smooth normal bump at \(t y\),
where \(t\geq 1\). Each derivative through order
\(d\) of the resulting test is bounded by a constant times the order
\(d+m+1\) supremum seminorm of the original test, the normal norm to power
\(m\), and \(t^{-1}\). The constant depends on the derivative order and the
chosen bump. `WeightedNormalCutoffStatement` records this estimate.

The product rule separates the derivatives of the cutoff and the test. At
most \(t^i\) is lost on the cutoff term of order \(i\). On its support the
normal norm is at most \(t^{-1}\), and Taylor's estimate for the flat test
supplies the normal norm to power \(m+i+1\). This retains the requested
normal weight and leaves a factor of \(t^{-1}\). Outside the cutoff support
all derivatives of that factor vanish.

This internal estimate controls the error from removing a shrinking
neighborhood of a lower Bruhat cell when the evaluation has polynomial growth
in the inverse normal distance.
