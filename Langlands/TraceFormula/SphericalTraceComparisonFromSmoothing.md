# Spherical replacement of factored smoothing traces

`SphericalTraceComparisonFromSmoothingStatement` combines the finite local
replacement with comparison of the positive smoothing powers. It uses a
cyclic unramified extension \(E/F\), the regular elementary pairs, and all
pairs \((\phi,b\phi)\) for the prescribed spherical base-change homomorphism.

Each side has a Hilbert sum and a symmetric trace-class smoothing
operator preserving its summands. The test operators are indexed by
the elementary weights and the spherical functions together. On each
lower summand and each twist-fixed upper summand, the compression of
the test operator times the \((k+1)\)-st smoothing power has a trace of
product form. One factor is the ordinary or twisted distribution of
the supplied generic irreducible admissible representation evaluated
at the local test. The other factor depends only on the summand and
\(k\). The compressed operator is zero on the other upper summands.

If the two traces at all elementary tests and all positive smoothing
powers agree up to a single scalar \(d\), the two traces at every spherical
pair with one smoothing factor agree up to \(d\). The proof assumes both
instances of `RegularElementaryJacquetTraceStatement`, both instances of
`UnramifiedWeylJacquetSupportStatement` and the extension instance of
`UnramifiedGenericSigmaNormalizationStatement`.

The proof multiplies the lower test operators by \(d\), using trace
linearity for the trace-class products and their compressions.
`compactOperatorTraceReplacement` reduces the desired equality to the
comparison on each nonzero smoothing eigenspace.
`finiteSmoothingTraceExpansion` gives one family of coefficients for
the elementary and spherical tests on each side. Removing the zero
terms leaves only the fixed indices upstairs. On the two resulting
finite sums, `regularElementarySphericalTraceReplacement` gives the
spherical equality. The compact operator replacement sums the
eigenspace traces, and trace linearity restores the scalar.

The operator step implements the spectral comparison using smoothing
powers. The finite local character comparison is Henniart–Lemaire (2011),
I.5.5, Théorème and Lemma 2, printed pp. 37–39 (PDF pp. 45–47).
Arthur–Clozel (1989), Chapter 1, §4, (4.6)–(4.7) and Lemma 4.10,
printed pp. 43–45 (PDF pp. 57–59), motivate the spectral comparison
through separation of the infinite components and finiteness at a
fixed level. The smoothing powers and their moment factorizations
are hypotheses of this operator formulation.
