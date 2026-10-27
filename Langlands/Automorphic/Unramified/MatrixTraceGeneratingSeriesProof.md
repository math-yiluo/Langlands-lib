# Matrix trace generating series proof

Worker 203 proves the complete published proposition
`Langlands.Automorphic.Unramified.MatrixTraceGeneratingSeriesStatement`
in the theorem `Langlands.Automorphic.Unramified.matrixTraceGeneratingSeries`.
The module imports the unchanged
`Langlands.Automorphic.Unramified.TraceGeneratingSeriesStatement` and its
helper `polynomialTraceSeries`, through the published
`Langlands.Automorphic.Unramified.PolynomialTraceGeneratingSeriesProof`,
whose binary product identity `polynomialTraceSeries_mul` it reuses. This is
an internal algebraic prerequisite for the determinant-product trace
equivalences discussed in [TraceAlgebraStatement](TraceAlgebraStatement.md);
no automorphic theorem or new original-literature claim is used.

Write \(G(P)=-X P'P^{-1}\) in \(\mathbb C[[X]]\), with the actual
polynomial-to-power-series coercion and formal-series operations, and
\(P_A=\det(1-XA)\) for the actual Mathlib `Matrix.charpolyRev`. The target
says that \([X^k]\,G(P_A)=\operatorname{tr}(A^k)\) for every \(n\), every
\(A\in M_n(\mathbb C)\) and every \(k>0\). The proof is spectral: both sides
are computed as the power sum \(\sum_r r^k\) over the roots \(r\) of the
characteristic polynomial of \(A\), counted with multiplicity. No Jacobi
formula or triangularization of matrices is used.

## Auxiliary declarations

`coeff_polynomialTraceSeries_one_sub_C_mul_X` proves, for \(r\in\mathbb C\)
and \(k>0\),
\[
  [X^k]\,G(1-rX)=r^k .
\]
The coerced series is \(1-rX\) and its formal derivative is \(-r\). The
geometric series \(\sum_{m\ge 0} r^mX^m\) (`PowerSeries.mk`) times
\(1-rX\) is \(1\), checked coefficientwise, so
`PowerSeries.inv_eq_iff_mul_eq_one` identifies it with \((1-rX)^{-1}\).
Hence \(G(1-rX)=X\cdot r\sum_m r^mX^m\), whose coefficient at \(j+1\) is
\(r\cdot r^j=r^{j+1}\). The case \(r=0\) is included.

`polynomialTraceSeries_multiset_prod` extends the published binary identity
\(G(PQ)=G(P)+G(Q)\) to a finite multiset of polynomials with constant
coefficient one: \(G(\prod_{P\in s}P)=\sum_{P\in s}G(P)\). Induction on the
multiset uses \(G(1)=0\) for the empty multiset. In the insertion step the
remaining product has constant coefficient one by
`Polynomial.coeff_zero_multiset_prod`. A multiset, rather than a finite set,
keeps repeated factors.

`charpolyRev_eq_prod_roots` proves, for every \(A\in M_n(\mathbb C)\),
\[
  P_A=\prod_{r}(1-rX),
\]
the product over the multiset of roots of `A.charpoly`. Since \(\mathbb C\)
is algebraically closed, the monic characteristic polynomial splits and is
\(\prod_r(X-r)\) (`Splits.eq_prod_roots_of_monic`). Mathlib's
`Matrix.reverse_charpoly` identifies `charpolyRev` with the reverse of the
characteristic polynomial. Reversal is multiplicative over the domain
\(\mathbb C[X]\) (`reverse_mul_of_domain`), the reverse of \(1\) is \(1\), and
the reverse of \(X-r\) is \(1-rX\); induction on the multiset of roots
finishes. For \(n=0\) the multiset is empty and both sides are \(1\).

`trace_pow_eq_of_isNilpotent_sub` proves that if \(g\) is an endomorphism
of a finite-dimensional complex vector space \(V\) and \(g-\mu\) is
nilpotent, then \(\operatorname{tr}(g^k)=\mu^k\dim V\). Induction on \(k\)
uses Mathlib's `LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent`,
which gives \(\operatorname{tr}(g^k g)=\mu\operatorname{tr}(g^k)\) because
\(g^k\) commutes with \(g\).

`trace_pow_eq_sum_roots_charpoly_pow` proves, for every \(A\) and every
\(k\),
\[
  \operatorname{tr}(A^k)=\sum_r r^k ,
\]
over the roots of `A.charpoly` with multiplicity. Let \(f\) be the linear
endomorphism `Matrix.toLin' A` of \(\mathbb C^n\); then
\(\operatorname{tr}(A^k)\) is the trace of \(f^k\), and \(f\) has the same
characteristic polynomial. Over \(\mathbb C\) the maximal generalized
eigenspaces \(V_\mu\) of \(f\) are independent and span \(\mathbb C^n\)
(`Module.End.iSup_maxGenEigenspace_eq_top`), so they form an internal
direct sum, and only finitely many are nonzero. Each \(V_\mu\) is invariant
under \(f^k\), and `LinearMap.trace_eq_sum_trace_restrict'` writes
\(\operatorname{tr}(f^k)\) as the sum of the traces of the restrictions over
the nonzero \(V_\mu\). On \(V_\mu\), the restriction of \(f^k\) is the
\(k\)-th power of the restriction of \(f\), and that restriction minus
\(\mu\) is nilpotent, so the previous lemma gives
\(\mu^k\dim V_\mu\). Mathlib's `LinearMap.finrank_maxGenEigenspace_eq`
identifies \(\dim V_\mu\) with the root multiplicity of \(\mu\) in the
characteristic polynomial. The same identification shows that \(V_\mu\neq0\)
exactly when \(\mu\) is a root. Grouping the power sum over the roots by
their counts (`Finset.sum_multiset_map_count`, `Polynomial.count_roots`)
gives the same finite sum. Singular and nonsemisimple matrices need no
special treatment: the root \(0\) contributes \(0^k\) times its
multiplicity, and nilpotent parts contribute no trace.

## Closed target and scope

`matrixTraceGeneratingSeries` introduces \(n\), \(A\), \(k\) and \(0<k\).
It rewrites \(P_A\) as \(\prod_r(1-rX)\). Every factor has constant
coefficient one, so the multiset additivity gives
\(G(P_A)=\sum_r G(1-rX)\). The coefficient map \([X^k]\) is additive. The
linear-factor lemma, which uses \(k>0\), turns each summand into \(r^k\),
and the trace lemma identifies \(\sum_r r^k\) with
\(\operatorname{tr}(A^k)\).

The theorem's complete type is exactly the closed published
`MatrixTraceGeneratingSeriesStatement`, with no theorem parameters or added
hypotheses. All natural ranks, including zero, all complex square matrices,
including arbitrary singular and nonsemisimple ones, and all positive
exponents are covered. The coefficient at zero is outside the statement:
there \(G(P_A)\) has coefficient \(0\) while \(\operatorname{tr}(A^0)=n\).

The proof uses environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and
Mathlib's polynomial splitting, reverse polynomial, formal-series inverse
and derivative, generalized eigenspace and trace theory. It introduces no
new axioms or proof holes.
