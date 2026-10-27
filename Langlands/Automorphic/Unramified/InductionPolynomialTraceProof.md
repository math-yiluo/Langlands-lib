# Polynomial substitution and weighted power traces

Author: Worker 355.

`Langlands.Automorphic.Unramified.inductionPolynomialTrace` proves the exact
closed proposition `InductionPolynomialTraceStatement`, imported unchanged
from [TraceAlgebraStatement](TraceAlgebraStatement.md). Write
\(P_A(T)=\det(1-TA)\), the actual Mathlib `Matrix.charpolyRev`. For every
finite family of complex square matrices \(A_i\), with ranks that may vary,
every complex square matrix \(B\), and positive natural numbers \(f_i\),
the theorem proves

\[
 P_B(T)=\prod_i P_{A_i}(T^{f_i})
 \quad\Longleftrightarrow\quad
 \forall k>0,\quad
 \operatorname{tr}(B^k)=
 \sum_i
 \begin{cases}
 f_i\operatorname{tr}(A_i^{k/f_i}),&f_i\mid k,\\
 0,&f_i\nmid k.
 \end{cases}
\]

The quotient is natural-number division in the original guarded expression.
There are no invertibility, determinant, semisimplicity, rank-sum or
field-extension hypotheses. Empty families, zero ranks and repeated entries
are included.

## Reused algebraic results and provenance

The proof uses the published definition
`polynomialTraceSeries P = -X * derivative P * P⁻¹` in complex formal power
series, denoted \(G(P)\) below. It imports
[PolynomialTraceGeneratingSeriesProof](PolynomialTraceGeneratingSeriesProof.md),
by Worker 397, and
[MatrixTraceGeneratingSeriesProof](MatrixTraceGeneratingSeriesProof.md),
by Worker 203. Their closed theorems supply, respectively:

- injectivity of \(G\) on polynomials with constant coefficient one and
  additivity of \(G\) over finite products of such polynomials;
- \([T^k]G(P_A)=\operatorname{tr}(A^k)\) for every complex square matrix
  and every positive \(k\).

This module derives the substitution law and then assembles the stated
equivalence from those results and Mathlib's formal power series API.
It proves the internal algebraic prerequisite described in the target
Markdown, without making a new original-literature or automorphic claim.
Formal differentiation and inversion are algebraic; no convergence
hypothesis is involved.

## Implemented substitution law

The private helpers use `PowerSeries.expand f hf`, the algebra homomorphism
substituting \(T^f\) for \(T\), with \(f\ne0\).
`expand_inv` proves that expansion commutes with inversion when the
original series has nonzero constant coefficient. It maps the inverse
equation through the homomorphism and uses uniqueness of the inverse.
`euler_derivative_expand` applies the formal chain rule and power rule to
obtain

\[
 T\,(\operatorname{expand}_f P)'=
 C(f)\operatorname{expand}_f(TP').
\]

Positivity justifies \(T T^{f-1}=T^f\).
`negative_log_derivative_expand` combines these two identities into
\(G(\operatorname{expand}_f P)=C(f)\operatorname{expand}_f G(P)\).
`coeff_negative_log_derivative_expand` applies
`PowerSeries.coeff_expand`: the coefficient at \(k\) is
\(f[T^{k/f}]G(P)\) if \(f\mid k\), and zero otherwise.
`coe_comp_X_pow` identifies polynomial composition with this expansion
after coercion to power series by comparing coefficients with
`Polynomial.coeff_expand`.

## Proof of the closed target

`inductionPolynomialTrace` introduces exactly the matrices, ranks and
positive integers quantified by the target. The constant coefficient of
every \(P_A\) is one, by `Matrix.eval_charpolyRev`. Substitution by a
positive power preserves that constant coefficient, as does the finite
product, including the empty product.

The local coefficient identity `hsubst` applies the private substitution
law to each \(P_{A_i}\). The identity `hsum` uses the published finite-product
additivity theorem and the published matrix coefficient theorem to obtain
the weighted trace sum for each positive \(k\). In the divisibility branch,
\(f_i\mid k\), \(k>0\) and \(f_i>0\) imply \(k/f_i>0\), as required by the
matrix coefficient theorem.

For the forward implication, equality of polynomials identifies the
coefficients of their trace series, and `hsum` yields the trace equations.
For the reverse implication, the trace equations and `hsum` give equality
of every positive coefficient. Both constant coefficients are zero directly
from the factor \(T\) in \(G\). Power series extensionality gives equality
of the trace series; the imported injectivity result for polynomials with
constant coefficient one gives the desired polynomial equality.

The final theorem has no parameters outside the imported closed
proposition and no conditional prerequisite. The module uses the prepared
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and introduces no axioms
or proof holes.
