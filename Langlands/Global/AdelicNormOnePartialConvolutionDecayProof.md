# Uniform rapid decay of norm-one partial convolutions

`Langlands.Global.normOnePartialConvolutionRapidDecay` proves
`Langlands.Global.NormOnePartialConvolutionRapidDecayStatement` at arbitrary
universe. For the positive rational quotient and height \(H\) of the
statement, write \(\Phi_\kappa v(y)\) for the integral against \(v\)
over the norm-one subgroup with kernel \(\kappa(n^{-1}y)\). The desired
function is \(\Phi_{\overline K}v\).
[Statement](AdelicNormOnePartialConvolutionDecayStatement.md)

## Proof

Complex conjugation preserves the adelic test-function conditions.
`IsAdelicTestFunction.exists_eq_sum_convolution` factors
\(\overline K=\sum_j\kappa_j\) with
\(\kappa_j=\phi_j\ast\psi_j\) and both factors test functions.
For right convolution \(R(k)f(y)=\int k(a)f(ya)\,da\), the norm-one
Fubini identity gives
\[
  \Phi_{\kappa_j}v=R(\psi_j\circ\mathrm{inv})(\Phi_{\phi_j}v).
\]
The inner partial convolution is continuous. The right-convolution
differentiation theorem makes \(\Phi_{\kappa_j}v\) adelically smooth.
Induction on the archimedean derivative word \(D\) transfers all derivatives
to the outer kernel, giving \(D\Phi_{\kappa_j}v=R(k_D)(\Phi_{\phi_j}v)\) for
a test kernel \(k_D\) depending on \(D\) and \(j\). The kernel is independent
of \(v\).

Apply the Fubini identity in reverse to obtain \(\Phi_{R(k_D)\phi_j}v\).
The new kernel is a test function by inversion and convolution closure.
`exists_normOnePartialConvolution_growth` bounds its partial convolution by
\(C_{j,D}H(y)^R\lVert v\rVert_2\) with the same exponent \(R\) for every
word and summand. The partial-convolution lemmas also give rational left
invariance, finite right level from \(\kappa_j\), and pointwise vanishing
of proper constant terms for \(v\) in the full cuspidal \(L^2\) submodule.
[Partial convolution](../Automorphic/GroupSchemeNormOnePartialConvolution.md)

For each \(j\), apply `adelicNormOneCuspidalFamilyTranslateDecay` to the
family indexed by the whole cuspidal submodule with size
\(v\mapsto\lVert v\rVert_2\). The set of norm-one representatives is common
to all \(j\) and all \(v\). Consequently, for each norm-one \(x\), one
rational \(q\) places \(qx\) in that set. Each summand has the bound
\[
  \lvert\Phi_{\kappa_j}v(qxb)\rvert H(qx)^m\le C_j\lVert v\rVert_2
  \qquad (b\in B).
\]
Add the bounds with the triangle inequality and use the finite sum identity
for partial convolutions. This gives the constant \(\sum_j C_j\) and the
same \(q\) for every class and every translate in \(B\).
[Compact-translate decay](AdelicNormOneCuspidalFamilyTranslateDecay.md)

## Provenance

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.12 obtains rapid decay of an alternating combination of constant terms
under uniform moderate growth. For a cuspidal function this combination
equals the function on the Siegel domain. In I.3.4 they apply I.2.12 after
compact smooth convolution in the proof of a vanishing criterion. The
uniform norm-one partial-convolution estimate is a derived application.
The proof above obtains the required derivative bounds via
Dixmier–Malliavin factorization and the growth estimate for norm-one
partial convolutions, then applies the compact-translate family estimate.

- I.2.12, printed pp. 34–35 (PDF pp. 17–18).
  `moeglin-waldspurger-1995-growth-and-constant-terms`,
  SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
  [Chapter I, Part 2](https://doi.org/10.1017/CBO9780511470905.004)
- I.3.4, printed pp. 45–46 (PDF pp. 6–7).
  `moeglin-waldspurger-1995-cuspidal-components`,
  SHA-256 `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`.
  [Chapter I, Part 3](https://doi.org/10.1017/CBO9780511470905.005)
