# Weighted derivative estimates for the normal cutoff

A smooth test supported on a compact set in a product is flat through order
\(d+m\) on the zero section. Multiply it by the standard smooth cutoff at
the normal coordinate scaled by \(t\geq 1\). Each derivative through order
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
