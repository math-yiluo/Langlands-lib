# Matrix and normalized polynomial trace generating series statements

Worker 597 states the internal interface prescribed by task
`5950a475-8abb-4450-8e53-eb3f8f8ef965`. The formulas were agreed by Worker 355
and Worker 397 and routed by Worker 398, who supplied the published helper.
The module
`Langlands.Automorphic.Unramified.TraceGeneratingSeriesStatement` defines
the two closed propositions below in namespace
`Langlands.Automorphic.Unramified`. Its entry declaration is
`MatrixTraceGeneratingSeriesStatement`; the same contribution also contains
`PolynomialTraceGeneratingSeriesStatement`.

These are internal derived prerequisites for the published
`EulerProductTraceStatement` and `InductionPolynomialTraceStatement`, whose
motivation is explained in the published
[TraceAlgebraStatement Markdown](TraceAlgebraStatement.md), especially its
“Original sources and derived correspondence” discussion. This contribution
does not claim a new reading of the original PDFs and requires no new
literature source. Both declarations are definitions returning `Prop`. They
supply neither proofs nor assumed results in structures, and they assume no
automorphic theorem.

## Imported helper and normalization

The unchanged published module
`Langlands.Automorphic.Unramified.TraceGeneratingSeries` defines
`polynomialTraceSeries (P : Polynomial ℂ) : PowerSeries ℂ` by the exact formula

```lean
-PowerSeries.X * PowerSeries.derivative (P : PowerSeries ℂ) *
  (P : PowerSeries ℂ)⁻¹
```

Write this series as \(G(P)(T)=-T P'(T)(P(T))^{-1}\) in
\(\mathbb C[[T]]\). The coercion, derivative and inverse are the actual
Mathlib polynomial-to-power-series map and formal-series operations. The
inverse is total, so the helper is defined for every complex polynomial;
without a nonzero constant term this notation does not assert a unit inverse
identity. The polynomial consumers below explicitly require constant term
one. This both provides an invertible series and fixes the scalar
normalization needed by uniqueness. The product clause retains that
hypothesis for every factor. The helper's Lean/Markdown pair is not edited.

## Matrix statement

The exact declaration is

```lean
def MatrixTraceGeneratingSeriesStatement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), 0 < k →
    PowerSeries.coeff k (polynomialTraceSeries A.charpolyRev) =
      Matrix.trace (A ^ k)
```

Here \(P_A(T)=\det(1-TA)\) is the actual Mathlib `Matrix.charpolyRev`, with
constant term one. The target states

\[
  \forall n\in\mathbb N,\ \forall A\in M_n(\mathbb C),\
  \forall k\in\mathbb N,\quad
  0<k \ \Longrightarrow\ [T^k]G(P_A)=\operatorname{tr}(A^k).
\]

The rank \(n\) may be zero, and every positive natural exponent \(k\) is
quantified. Matrices may be singular or nonsemisimple. No determinant,
diagonalizability, positive-rank or other extra hypothesis occurs.
At rank zero the target compares the positive coefficients of \(G(1)\)
with the trace of the empty matrix power, both zero. The statement makes no
claim about the coefficient at \(k=0\). Matrix powers, traces and normalized
characteristic polynomials are Mathlib objects; no surrogate matrix
interface is introduced.

## Normalized polynomial statement

The exact declaration is

```lean
def PolynomialTraceGeneratingSeriesStatement : Prop :=
  (∀ (P Q : Polynomial ℂ), P.coeff 0 = 1 → Q.coeff 0 = 1 →
    (polynomialTraceSeries P = polynomialTraceSeries Q ↔ P = Q)) ∧
  (∀ (a : ℕ) (P : Fin a → Polynomial ℂ), (∀ i, (P i).coeff 0 = 1) →
    polynomialTraceSeries (∏ i, P i) = ∑ i, polynomialTraceSeries (P i))
```

The first conjunct universally quantifies two complex polynomials with
constant term one and states

\[
  P(0)=Q(0)=1\quad\Longrightarrow\quad
  \bigl(G(P)=G(Q)\ \Longleftrightarrow\ P=Q\bigr).
\]

The equality of \(G(P)\) and \(G(Q)\) is equality of complete formal power
series. Constant polynomials are included; normalization then forces such
a polynomial to be one. There is no degree or nonconstant hypothesis.

The second conjunct quantifies every \(a\in\mathbb N\) and every family
\(P:\mathrm{Fin}(a)\to\mathbb C[T]\) whose members have constant term one:

\[
  \bigl(\forall i<a,\ P_i(0)=1\bigr)
  \quad\Longrightarrow\quad
  G\!\left(\prod_{i<a}P_i\right)=\sum_{i<a}G(P_i).
\]

Repeated factors and the empty family are allowed. When \(a=0\), the
product is one and the sum is zero, so the clause includes \(G(1)=0\).
The conjunction contains the complete universally quantified targets,
without external parameters or hidden hypotheses.

## Proof and dependency boundary

This module imports only the published helper and
`Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`, in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. No axioms or proof holes are added.
The two propositions remain separate proof obligations. Proving them would
supply formal-series algebra for the existing trace-algebra targets; this
statement contribution itself proves no matrix identity, polynomial
uniqueness theorem, product theorem, or automorphic result.
