# Extending tests by a fixed kernel on a second factor

For open sets \(U\subset E\) and \(V\subset W\) in real normed spaces, let
\(\psi\) be a smooth compactly supported test on \(V\) with values in the
continuous linear maps \(A\to F\). The map `productKernelTestCLM ψ`
sends an \(A\)-valued test \(\phi\) on \(U\) to the \(F\)-valued test
\((x,y)\mapsto\psi(y)(\phi(x))\) on \(U\times V\).

The support lies in the product of the compact supports of \(\phi\) and
\(\psi\). With both supports fixed, the product rule for continuous
linear map evaluation bounds each derivative seminorm of the output by
a constant times the maximum of the input seminorms up to that order.
The two projections have operator norm at most one, so precomposition
with either projection does not increase the corresponding pointwise
derivative norm. Mathlib's `TestFunction.limitCLM` assembles the
continuous real-linear maps from the fixed-support spaces.

This internal construction supplies extensions of test functions from
one factor when the prescribed transverse data can be represented by a
fixed operator-valued kernel on the other factor.
