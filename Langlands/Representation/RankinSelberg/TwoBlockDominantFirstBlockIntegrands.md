# Dominant first-block scalar and Jacobian bridges

This is derived infrastructure for the first-block calculation of JPSS,
*Rankin–Selberg Convolutions* (1983), Section 4.9, printed pp.416–418, used in
Section 4.10(2), printed p.419. The general complementary row parameters and the
interfaces below are internal consequences of the published matrix definitions,
section covariance, and rectangular Haar scaling.

Write \(a=m_0+1\), \(b=m_1+1\), \(c=j+k+1\), and \(a+b=t+1\).
`firstBlockUpperValue` is the representative scalar
\[
 f[g;1,1]\,W(R(X)\operatorname{diag}(g,I_c))
 |\det g|^{s-c/2+j}.
\]
The exponent records the Jacobian needed when moving the external rectangle to
the left. Defining this scalar does not itself assert that this earlier move has
been carried out in any quotient integral.

`firstBlockFiberIntegrand` names the actual smaller JPSS integrand with the
translated test function and the actual first-block coefficient.
`firstBlockUpperValue_fiber` evaluates the upper scalar at
\(g=\operatorname{diag}(v,I_b)R(Z)g_0\) and \(X=(U,Y)\).
The actual matrix factorization replaces the large matrix by the smaller JPSS
matrix with rectangle obtained by joining \(Z\) and \(Uv+YZ\), followed by
\(R(0,Y)\operatorname{diag}(g_0,I_c)\). The test function is right translated by
this latter matrix. The second function is the actual first-block coefficient
obtained by contracting the second tensor factor of \(f(g_0)\).

The formula retains the base-point weight
\(|\det g_0|^{s-c/2+j}\) and an extra \(|\det v|^j\).
Its smaller JPSS integrand has parameters \(j_{\rm small}=b+j\),
\(k_{\rm small}=k\), and exponent \(s-(b+c)/2\). Section covariance contributes
\(|\det v|^{-b/2}\); elementary addition of determinant exponents proves the
displayed normalization.

`firstBlockRowJacobian` identifies the exact inverse determinant factor from the
supplied-Haar affine row change with \(|\det v|^{-j}\).

`integral_firstBlockUpperValue` applies that row change to the fiber formula.
For the same supplied scalar Haar \(\nu\), it proves
\[
\int_U \operatorname{UpperValue}
 \bigl(\operatorname{diag}(v,I_b)R(Z)g_0,(U,Y)\bigr)\,dU
 =
 |\det g_0|^{s-c/2+j}
 \int_T \operatorname{SmallIntegrand}(v,Z,Y,g_0,T)\,dT.
\]
The proof pulls out the constant weights, applies the established affine
substitution, and adds the exponents \(j\) and \(-j\). It is a total Bochner
identity, with no convergence premise or conclusion.

`integrable_firstBlockUpperValue_iff` separately proves equivalence of absolute
integrability of these two row fibers. Both determinant weights are nonzero, so
constant multiplication preserves integrability; the established affine
integrability equivalence then supplies the result. No inference of
integrability from an equality of total integrals is used.

All spectral parameters and supplied block functionals, including zero, are
retained. No convergence, quotient disintegration, functional equation, or
Laurent identity is asserted here.
