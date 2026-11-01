# Boundary cases of canonical Euclidean scalar regularity

This helper module of `Langlands.Analysis.ScalarEllipticAnalyticityProof`
specializes the published zero-dimension and zero-order scalar regularity
theorems to the canonical Euclidean assertion
`CanonicalEuclideanScalarEllipticAnalyticityStatement d r`. It then reduces
that assertion to positive dimension and positive order.

## Declarations

- `canonicalEuclideanScalarEllipticAnalyticity_dimension_zero (r : ℕ)` proves
  `CanonicalEuclideanScalarEllipticAnalyticityStatement 0 r`. It discards the
  premise that the operator's basis is the canonical basis. It then applies the
  published `scalarEllipticAnalyticity_dimension_zero` with
  `E = EuclideanSpace ℝ (Fin 0)`, which holds for every actual basis.
- `canonicalEuclideanScalarEllipticAnalyticity_order_zero (d : ℕ)` proves
  `CanonicalEuclideanScalarEllipticAnalyticityStatement d 0` in the same way,
  from the published `scalarEllipticAnalyticity_order_zero` with
  `E = EuclideanSpace ℝ (Fin d)`.
- `canonicalEuclideanScalarEllipticAnalyticity_of_positive` takes as an
  explicit premise the canonical assertion for every `d r` with `0 < d` and
  `0 < r`. It concludes the canonical assertion for all `d r : ℕ`. The proof
  splits `d` into `0` and `d + 1`, using the dimension-zero case for `0`. It
  then splits `r` into `0` and `r + 1`, using the order-zero case for `0`.
  The remaining case `(d + 1, r + 1)` is given by the premise.

All three keep the canonical statement's actual operator, its open domain, its
coefficient analyticity, ellipticity, genuine smoothness `ContDiffOn ℝ ∞` and
full homogeneous equation. The domain is real and the values are complex.
The module proves no positive-dimension, positive-order regularity and uses no
analytic estimate.

## Imports and provenance

The module imports the published proof module
`Langlands.Analysis.ScalarEllipticAnalyticityDegenerate` and the published
statement module `Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransportStatement`,
which defines the canonical assertion. The zero cases are the elementary
degenerate adaptation recorded in that proof module. The scalar
Morrey–Nirenberg route (1957, §5), described in
`ScalarEllipticAnalyticityProof.md`, concerns only positive dimension and
positive order. This case split is internal and is not taken from the
literature.

Worker 116 wrote the Lean code in a shared draft for this task, and Worker 1130
rewrote this explanation for submission.
