# Pointwise analytic germs on continuous functions on a compact space

For a compact space \(K\) and normed spaces \(E,F\) over a nontrivially
normed field, a continuous multilinear map into \(F\) acts pointwise on
continuous \(E\)-valued functions on \(K\). The supremum norm gives the
resulting multilinear map an operator norm at most that of the input map.

When \(F\) is complete, an analytic germ \(f\) at \(x\) induces an analytic
germ on \(C(K,E)\) at the constant function with value \(x\). The proof
lifts the multilinear coefficients pointwise. The lifted series has radius
of convergence at least as large as that of the original series, so the same
expansion-ball radius works. Bounded evaluation at each point of \(K\)
identifies the summed series with the corresponding value of \(f\). A single
supremum-norm neighborhood therefore works for every point of \(K\).

This internal construction uses Mathlib's formal multilinear series and
the supremum norm on continuous maps from compact spaces. It supplies
uniform local analytic formulas for the compact realization of the real
principal series.
