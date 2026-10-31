# Scalar elliptic analytic regularity in zero dimension or zero order

`Langlands.Analysis.ScalarEllipticAnalyticityDegenerateStatement E` is the
following proposition, with `E : Type v`, `[NormedAddCommGroup E]` and
`[NormedSpace ℝ E]`:

```lean
(∀ r : ℕ, ScalarEllipticAnalyticityStatement E 0 r) ∧
  (∀ d : ℕ, ScalarEllipticAnalyticityStatement E d 0)
```

The first conjunct covers dimension zero at every natural differential
order; the second covers order zero at every natural dimension. Both
include the case of dimension and order zero. The original real normed
space `E` is arbitrary in universe `v`; its norm, topology and real scalar
structure are unchanged.

Each constituent is the exact specialization of the published
`Langlands.Analysis.ScalarEllipticAnalyticityStatement`. For every actual
`D : CoordinateScalarOperator E d r`, set `S : Set E` and function
`F : E → ℂ`, that assertion states that openness of `S`,
`D.AnalyticCoefficientsOn S`, `D.IsEllipticOn S`,
`ContDiffOn ℝ ∞ F S`, and the full homogeneous equation
`∀ x ∈ S, D.action F x = 0` imply `AnalyticOnNhd ℝ F S`.
Here `∞` denotes genuine smooth order in the imported `ContDiff` scope.
The operator retains its actual finite real basis, complex coefficients
and values, real iterated Fréchet derivatives through every order up to
`r`, and symbol nonvanishing on every nonzero real continuous covector.
The conclusion is real analyticity near every point of `S` in the
original norm. Every open domain is covered, with no additional function
hypothesis or analytic-solution certificate.

This is an internal statement by Worker 116 isolating the boundary cases
of the scalar regularity problem. Its provenance is the exact
specialization and conjunction of the existing scalar statement; it
claims no separate literature theorem. Worker 347 reused Worker 116's
Lean definition unchanged and expanded this documentation. The imported
published pairs are unchanged.

The file defines the proposition only. It proves neither boundary case
and introduces no positive-dimension, positive-order regularity assertion.
An exact-target proof is separate work after publication of this statement.
