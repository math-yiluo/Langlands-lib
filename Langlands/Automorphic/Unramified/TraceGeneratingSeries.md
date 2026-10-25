# Polynomial trace generating series

Worker 398 implements the common helper formula agreed by Worker 355 and
Worker 397. This is an internal definition contribution. The module
`Langlands.Automorphic.Unramified.TraceGeneratingSeries` defines
`Langlands.Automorphic.Unramified.polynomialTraceSeries`.

For every actual Mathlib polynomial `P : Polynomial ℂ`, the exact definition is

```lean
noncomputable def polynomialTraceSeries (P : Polynomial ℂ) : PowerSeries ℂ :=
  -PowerSeries.X * PowerSeries.derivative (P : PowerSeries ℂ) *
    (P : PowerSeries ℂ)⁻¹
```

Thus, in formal-variable notation, its value is
\[
G(P)(T)=-T\,P'(T)\,(P(T))^{-1}\quad\text{in }\mathbb C[[T]].
\]
The coercion embeds the polynomial in Mathlib's formal power series, and the
derivative and inverse are Mathlib's operations on those series. This is a
total, noncomputable function on all complex polynomials. No nonvanishing,
normalization, matrix, rank, or semisimplicity hypothesis is part of its type.
Without a nonzero constant term, the displayed inverse still means Mathlib's
total formal-series inverse; the definition does not assert a unit inverse
identity in that case. All intended uniqueness and product consumers
explicitly require `P.coeff 0 = 1` for each input polynomial.

The provenance is internal and derived: this helper names the formal-series
expression motivating the algebraic targets in the published
[TraceAlgebraStatement Markdown](TraceAlgebraStatement.md), especially its
“Original sources and derived correspondence” discussion. That existing
document supplies the motivating source discussion; this contribution does
not claim a new reading of the original PDFs and needs no new literature
source. It introduces no axioms, structures carrying assumed results, or
automorphic assumptions.

For a matrix `A`, the intended later prerequisite identifies positive
coefficients of `G(A.charpolyRev)` with `Matrix.trace (A ^ k)`. That identity,
normalized-polynomial uniqueness, and finite-product additivity are separate
statement and proof obligations. This definition proves none of them and
asserts no automorphic theorem. The matrix consumers use actual Mathlib
matrices, characteristic polynomials, powers, and traces.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`; the imports are
`Mathlib.Basic.Complex.Basic` and
`Mathlib.RingTheory.PowerSeries.Derivative`.
