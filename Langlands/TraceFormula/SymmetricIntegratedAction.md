# Symmetry of integrated isometric actions with star-invariant weights

Let \(G\) be a group with a measurable structure for which inversion is measurable, and let
\(\mu\) be an inversion-invariant measure on \(G\). Let \(\pi\) be a representation of
\(G\) by bounded operators on a complex Hilbert space \(H\), with \(\|\pi(g)x\| = \|x\|\)
and strongly measurable orbits. For an integrable weight \(f\) on \(G\), the Library's
`integratedIsometricAction` is the bounded operator
\[
  \pi(f)x = \int_G f(g)\,\pi(g)x \, d\mu(g).
\]

## Statement

`SymmetricIntegratedActionStatement` asserts that \(\pi(f)\) is symmetric when
\(f(g^{-1}) = \overline{f(g)}\) for all \(g\).

## Proof

`inner_map_inv_eq` shows that \(\langle x, \pi(g^{-1})y\rangle = \langle \pi(g)x, y\rangle\).
Each \(\pi(g)\) is a linear isometry, so it preserves inner products, and
\(\pi(g)\pi(g^{-1}) = 1\).

For the operator, inner products commute with the Bochner integral (`integral_inner`) and
with conjugation (`integral_conj`). Inversion invariance of \(\mu\)
(`integral_inv_eq_self`) replaces \(g\) by \(g^{-1}\). The two hypotheses then turn
\[
  \langle x, \pi(f)y\rangle = \int f(g^{-1})\,\langle x, \pi(g^{-1})y\rangle\,d\mu(g)
\]
into the conjugate of \(\int f(g)\,\langle y, \pi(g)x\rangle\,d\mu(g)\), which is
\(\langle \pi(f)x, y\rangle\).

This is the standard fact that \(\pi(f)^* = \pi(f^*)\) with \(f^*(g) = \overline{f(g^{-1})}\)
for a unitary representation and an inversion-invariant measure. The proof is internal.
Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace
formula* (1989), Chapter 1, §4, printed pp. 43–45, motivates its use: their comparison of
the trace formulas varies the archimedean components of the test functions. This symmetry
serves an internal smoothing approach to that comparison, in which the smoothing operators
must be self-adjoint; the cited pages do not contain this step.

Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
