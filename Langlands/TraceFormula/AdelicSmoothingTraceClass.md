# Trace class of fixed-level adelic smoothing tensors

Work on the cuspidal Hilbert space `fullAEL2CuspidalSubmodule` for an
affine connected reductive group over a number field. Use the split
adelic product and its product Haar measure as in
`AdelicFixedLevelSmoothing`. Let \(f\) be continuous and compactly
supported on the infinite factor. Write \(R(g,k)\) for the integrated
operator of \(f^{*(k+1)}\otimes g\) for a finite Hecke test \(g\).

For a compact open subgroup \(K\) of the finite factor, let \(e_K\) be
its normalized indicator. `AdelicSmoothingTraceClassStatement` assumes
that \(R(e_K,0)\) is trace class and that \(g\) is invariant on both sides
under \(K\). It concludes that \(R(g,k)\) is trace class for every
\(k\geq 0\).

In `adelicSmoothingTraceClass`, let \(B(g)\) be the integrated operator
for the restriction of the right action to the finite factor.
The convolution identity for integrated actions and left averaging
give \(B(e_K)B(g)=B(e_K*g)=B(g)\). Fubini's theorem and the commutation
of a bounded linear map with a Bochner integral express \(R(g,0)\)
as the infinite integral applied to \(B(g)\). The averaging identity
therefore gives \(R(g,0)=R(e_K,0)B(g)\). Right invariance and
`adelicFixedLevelSmoothingPowers` give
\(R(g,k)=R(g,0)R(e_K,0)^k\). The trace-class ideal property applies
to both compositions.

This operator argument supplies trace-class factors for the global
trace comparison motivated by Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Ch. 1,
§4, formulas (4.4)–(4.7), printed pp. 43–44 (PDF pp. 57–58).

Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
