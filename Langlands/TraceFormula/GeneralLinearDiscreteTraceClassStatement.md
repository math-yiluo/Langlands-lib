# Trace class on the full discrete automorphic spectrum of `GL_n`

`Langlands.TraceFormula.GeneralLinearDiscreteTraceClassStatement` is the `GL_n`
specialization of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 9.1.4 (printed p. 242, PDF p. 254). The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Chapter 9, The Cuspidal Spectrum](https://link.springer.com/chapter/10.1007/978-3-031-41153-3_9)

For a number field \(F\) and \(n>0\), let \(G\) be the group scheme
`GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
For every `hG : IsConnectedReductive G` and every complex function \(f\) on
\(G(\mathbb A_F)\) satisfying `IsAdelicTestFunction F G f`, the proposition
asserts `IsTraceClass (canonicalDiscreteIntegratedAction F G hG f hf)` for
every `hf` witnessing integrability of \(f\) for the adelic `Measure.haar`.
Continuity and compact support give such a witness.

Write \([G]=A_G G(F)\backslash G(\mathbb A_F)\), where \(A_G\) is the
positive real part of the canonical split centre. The operator is the
compression of the integrated right regular action to
`discreteSpectrum F G hG` in `Lp ℂ 2 (canonicalMeasure F G)`.
This is the closed span of all irreducible subrepresentations of \(L^2([G])\),
including the residual spectrum. The statement applies at every finite level
allowed by `IsAdelicTestFunction` and to arbitrary smooth archimedean slices.

Getz–Hahn take tests on \(A_G\backslash G(\mathbb A_F)\) (§9.1, printed pp.
239–240). Under the identification of that quotient with the norm-one group,
the corresponding test is `canonicalNormOneAverage F G hG f`, given by
\(x\mapsto \int_{A_G} f(ax)\,da\). The support of the average lies in the
compact image of the support of \(f\). Integration preserves archimedean
smoothness by differentiation under the integral over the compact projection
of that support onto \(A_G\). Right invariance at a finite adelic compact
open subgroup gives a finite expansion over its cosets on the projected
support, placing the average in the algebraic test-function tensor product
used in §9.1.

The Haar measure \(da\) in the average is normalized so that its product with
`Measure.haar` on the norm-one group gives the adelic `Measure.haar` under
multiplication. Since \(A_G\) acts trivially on \([G]\), Fubini identifies
the integrated action of \(f\) with the integrated action of the quotient
test. On the invariant discrete subspace, its compression is the restriction
in Theorem 9.1.4.
