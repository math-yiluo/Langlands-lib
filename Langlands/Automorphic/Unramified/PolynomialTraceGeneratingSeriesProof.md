# Normalized polynomial trace generating series proof

Worker 397 proves the complete published proposition
`Langlands.Automorphic.Unramified.PolynomialTraceGeneratingSeriesStatement`
in the theorem `Langlands.Automorphic.Unramified.polynomialTraceGeneratingSeries`.
The module imports the unchanged
`Langlands.Automorphic.Unramified.TraceGeneratingSeriesStatement` and uses
its published helper `polynomialTraceSeries`. This is an internal algebraic
prerequisite for the determinant-product trace equivalences discussed in
[TraceAlgebraStatement](TraceAlgebraStatement.md); no automorphic theorem
or new original-literature claim is used.

Write \(G(P)=-X P'P^{-1}\) in \(\mathbb C[[X]]\), with the actual
polynomial-to-power-series coercion and formal-series operations. All
normalization hypotheses below mean `P.coeff 0 = 1`. They make the series
invertible and fix the constant scalar needed for uniqueness.

## Auxiliary declarations

`polynomialTraceSeries_coeff_zero` proves that the coefficient at zero of
\(G(P)\) vanishes for every complex polynomial, by the initial factor \(X\).
`polynomialTraceSeries_one` proves \(G(1)=0\).

`polynomialTraceSeries_mul` proves
\[
  G(PQ)=G(P)+G(Q)
\]
when both constant coefficients are one. The formal derivative product
rule and the inverse-of-product identity expand the left side. Commutative
ring rearrangement puts each term next to a factor \(PP^{-1}\) or
\(QQ^{-1}\), and the unit cancellation identities reduce both factors to
one.

`polynomialTraceSeries_injective_normalized` proves, for normalized \(P,Q\),
\[
  G(P)=G(Q)\quad\Longleftrightarrow\quad P=Q.
\]
For the forward direction, write \(p,q\) for their formal series. Cancel
the nonzero factor \(-X\) to obtain \(p'p^{-1}=q'q^{-1}\).
Multiplying and rearranging gives \(qp'=pq'\). The formal derivative
product and inverse rules then give
\[
  (pq^{-1})'=q^{-2}(qp'-pq')=0.
\]
The ratio \(pq^{-1}\) has constant coefficient one. Over \(\mathbb C\),
Mathlib's `PowerSeries.derivative.ext` says that equal derivatives and
equal constant coefficients determine the series, so \(pq^{-1}=1\).
Multiplication by \(q\) gives \(p=q\), and injectivity of the
polynomial-to-series coercion gives \(P=Q\). The reverse implication is
substitution.

`polynomialTraceSeries_prod` extends the binary product identity to every
finite set of normalized polynomials. Induction on the finite set uses
\(G(1)=0\) in the empty case. For insertion, the binary identity applies
to the inserted polynomial and the remaining product; the remaining
product has constant coefficient one because evaluation at zero
commutes with finite products.

## Closed target and scope

`polynomialTraceGeneratingSeries` combines normalized injectivity with
the finite-product result specialized to the full set of `Fin a`. Its
complete type is exactly the closed published
`PolynomialTraceGeneratingSeriesStatement`, with no theorem parameters
or added hypotheses.

All normalized complex polynomials are covered, including the constant
polynomial one, and all natural family sizes are covered, including zero
and repeated factors. No degree, matrix-realizability or determinant
hypothesis is used. The module establishes the scalar statement and its
displayed helpers; the arbitrary-matrix coefficient law and the final
Euler-product equivalence remain separate proof obligations.

The proof uses environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and
Mathlib's formal-series inverse and derivative theory. It introduces no
new axioms or proof holes.
