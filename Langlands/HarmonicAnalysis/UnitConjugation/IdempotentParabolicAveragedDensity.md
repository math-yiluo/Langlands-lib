# Density for the compactly averaged parabolic constant term

Let \(A\) be a finite-dimensional ultrametric normed algebra over a
proper nontrivially normed field \(F\), with the module topology. For an
idempotent \(e\) put \(M=\operatorname{Cent}_A(e)\) and \(N=eA(1-e)\).
Let \(K\le A^\times\) be a compact open subgroup. Suppose the unit value
map is an open embedding. Use additive Haar measures \(\mu,\mu_M,\nu\)
on \(A,M,N\), and let \(\mu_K\) be the restriction of two-sided unit Haar
to \(K\) in its subtype.

For a locally \(\mu_M\)-integrable function \(\theta\) on \(M\),
`idempotentParabolicAveragedDensity` gives a locally \(\mu\)-integrable
function \(r\) on \(A\) such that
\[
 \int_A r(x) f(x)\,d\mu(x)
   = \int_M \theta(Y)
     \int_N\int_K f(k^{-1}(Y+Z)k)\,d\mu_K(k)\,d\nu(Z)\,d\mu_M(Y)
\]
for every Schwartz–Bruhat test \(f\). The inner two integrals are the
compactly averaged constant term in `IdempotentParabolicAveragedDensityStatement`.

The proof replaces \(\theta\) by a measurable representative of its
almost-everywhere class for the change of variables. The test kernel
\((Y,Z,k)\mapsto f(k^{-1}(Y+Z)k)\) has compact support. The map to
\((k^{-1}(Y+Z)k,k)\) admits a continuous left inverse obtained by conjugating
back and projecting to the Levi and upper blocks. The pullback of the
Levi weight is locally integrable by restricting to rectangles containing
compact sets. Multiplication by the kernel then gives an integrable
function, which justifies Bochner Fubini.

Haar measure on \(K\) is invariant under inversion. The unit values of
\(k^{-1}\) carry \(\mu_K\) to a scalar multiple of additive Haar
restricted to the compact open image of \(K\). Reordering the product
measures and taking these unit coordinates gives precisely the
weighted integral of `idempotentParabolicDensity`. Its ambient density,
scaled by the compact-coordinate Haar factor, has the required pairing.

Harish-Chandra proves the density transfer for invariant Levi functions
using Weyl integration in *Admissible invariant distributions on
reductive \(p\)-adic groups*, §1.4, Lemma 1.13, printed p. 10. The proof
here uses the submersion and locally integrable weighted pushforward of
`IdempotentParabolicDensity`, which apply to locally integrable weights
on the Levi.
