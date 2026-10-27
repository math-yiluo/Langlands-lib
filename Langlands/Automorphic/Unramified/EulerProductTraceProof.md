# Determinant-product equality and positive power traces

Worker 397 proves the exact published proposition
`Langlands.Automorphic.Unramified.EulerProductTraceStatement` in the theorem
`Langlands.Automorphic.Unramified.eulerProductTrace`. Its complete type is that
closed proposition, imported unchanged from `TraceAlgebraStatement`, with no
additional hypotheses.

For independently varying natural ranks and finite families of complex matrices,
write \(P_A(X)=\det(1-XA)\), the actual Mathlib `Matrix.charpolyRev`. The theorem
states
\[
 \prod_{i<a}P_{A_i}=\prod_{j<b}P_{B_j}
 \quad\Longleftrightarrow\quad
 \forall k>0,\quad
 \sum_{i<a}\operatorname{tr}(A_i^k)
   =\sum_{j<b}\operatorname{tr}(B_j^k).
\]

## Imported algebraic results

The existing `polynomialTraceSeries` is
\(G(P)=-X P'P^{-1}\) in \(\mathbb C[[X]]\), using the polynomial coercion,
formal derivative, and formal-series inverse. This proof reuses the published
results by their Lean names:

- `polynomialTraceSeries_prod` in
  [PolynomialTraceGeneratingSeriesProof](PolynomialTraceGeneratingSeriesProof.md)
  gives \(G(\prod_i P_i)=\sum_i G(P_i)\) when every factor has constant term one.
- `polynomialTraceSeries_injective_normalized` in the same module gives
  \(G(P)=G(Q)\Longleftrightarrow P=Q\) when both constant terms are one.
- `matrixTraceGeneratingSeries` in
  [MatrixTraceGeneratingSeriesProof](MatrixTraceGeneratingSeriesProof.md)
  gives \([X^k]G(P_A)=\operatorname{tr}(A^k)\) for every natural rank, every
  complex square matrix, and every positive \(k\).
- `polynomialTraceSeries_coeff_zero` gives \([X^0]G(P)=0\) for every \(P\).

The matrix coefficient identity is thus an imported theorem, not a hypothesis
of this proof. No helper, statement, or imported proof pair is changed.

## Implemented proof

The local lemma `family_coeff` first applies finite-product additivity to the
family of reversed characteristic polynomials. Each factor has constant
coefficient one, as follows from `Matrix.eval_charpolyRev` at zero and
`Polynomial.coeff_zero_eq_eval_zero`. Applying the additive coefficient map to
the resulting finite sum, then applying `matrixTraceGeneratingSeries` to each
summand, proves
\[
 [X^k]G\!\left(\prod_iP_{A_i}\right)
   =\sum_i\operatorname{tr}(A_i^k)\qquad(k>0).
\]
The same normalization and `Polynomial.eval_prod` show that each of the two
polynomial products has constant coefficient one.

For the forward implication, congruence applies \(G\) and then the \(k\)-th
coefficient map to the assumed polynomial equality. The local lemma rewrites
the two coefficients as the required trace sums.

For the reverse implication, `PowerSeries.ext` reduces equality of the two
trace series to equality of every coefficient. At zero both coefficients
vanish, by the initial factor \(X\) in \(G\). At each successor index the local
lemma rewrites the coefficients as trace sums, and the assumed equality for
that positive exponent applies. Normalized injectivity then recovers equality
of the two polynomial products.

## Scope and provenance

The argument covers every finite family size, including empty families, and
every natural rank, including zero. Family values need not be distinct.
Singular and nonsemisimple matrices are included by the imported matrix theorem.
There is no invertibility, nonzero-determinant, semisimplicity, or equal-rank
assumption. Only positive power traces occur; zero eigenvalues contribute
neither a nonconstant factor to \(P_A\) nor a positive power trace, so equality
of ranks is not a conclusion.

This is the internal formal-series derivation motivated in the unchanged
[TraceAlgebraStatement](TraceAlgebraStatement.md). The imported scalar proof uses
formal differentiation and characteristic-zero uniqueness, and the imported
matrix proof establishes the coefficient identity through characteristic roots
and generalized eigenspaces. The present module assembles those results and
makes no new assertion about the original automorphic literature, rigidity, or
transfer. It proves only the Euler-product trace member of the three-part
`TraceAlgebraStatement`.

The proof uses environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, introduces no
axioms, and contains no proof holes.
