# Positive smoothing powers at a common finite level

Let \(A\) and \(B\) be locally compact second-countable groups equipped
with left Haar measures. They represent the infinite and finite factors
of an adelic group. Fix a continuous compactly supported test \(f\) on
\(A\) and a compact open subgroup \(K\) of \(B\). Let \(e_K\) be the
normalized subgroup indicator and let \(g\) be a test in the Haar Hecke
algebra of \(B\) that is right \(K\)-invariant. Write \(R\) for the
bounded integrated action of a norm-preserving representation of
\(A\times B\) with almost everywhere strongly measurable orbits.

Set \(T=R(f\otimes e_K)\).
`FixedLevelSmoothingPowersStatement` says that for a bounded operator
\(U\) commuting with \(T\) and every \(k\geq 0\),
\[
   (R(f\otimes g)U)\,T^k=R(f^{*(k+1)}\otimes g)\,U.
\]
The identity operator gives the ordinary formula. The same \(g\) occurs
at every power.

`convolutionIntegral_prod_tensor` computes convolution coordinate by
coordinate for the product Haar measure. A further \(f\) adds one
infinite convolution factor. On \(B\),
`HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant` gives
\(g*e_K=g\). `integratedActionConvolution` sends this tensor convolution
to operator multiplication. Induction and commutation with \(U\) give
the stated formula.

`integratedIsometricAction_pullback` identifies these operators with
integrated operators under a measure-preserving group equivalence, by
change of variables. `commute_integratedIsometricAction_of_invariant`
gives the twist commutation when the test is invariant under the
measure-preserving automorphism and \(U\) intertwines the actions
related by that automorphism.

This construction supplies the changing infinite test and fixed finite
test in the local trace comparison. The ordinary and twisted
cuspidal spectral expressions in Arthur–Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989),
Chapter 1, §4, printed pp. 43–44, motivate the use of the product
normalization and matching infinite factors. The power formula follows
from the convolution identities above.
