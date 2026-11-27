# Determinants over the dual numbers

Module `Langlands.Algebra.DualNumberDeterminant`, namespace
`Langlands.Algebra.DualNumberDeterminant`.

`det_eq_of_map_fst_eq_one`: let `A` be a commutative ring, `n` a finite type, and `M` an
`n × n` matrix over the dual numbers `A[ε]` whose reduction modulo `ε` (`M.map fst`) is the
identity matrix. Then

```text
det M = 1 + ε · tr N,   N = M.map snd   (the matrix of ε-coefficients of M).
```

This is the first-order case of Jacobi's formula for the derivative of the determinant.

## Proof

Write `N = M.map snd`. The algebra map `e : A[X] → A[ε]`, `X ↦ ε` (`aeval ε`), sends the
polynomial matrix `1 + X • N.map C` entrywise to `M`. On the diagonal the constant part is `1`,
off the diagonal it is `0`, and the `ε`-part of `e (X · C a)` is `a`. Since ring maps commute
with determinants (`RingHom.map_det`), `det M = e (det (1 + X • N.map C))`. Mathlib's
`Matrix.det_one_add_X_smul` writes this polynomial as `1 + tr N • X + q · X²`. Applying `e`
kills the last term because `ε² = 0` (`DualNumber.eps_mul_eps`), leaving `1 + tr N • ε`.
Comparing the two components gives the claim.

## Provenance

Internal. A standard identity; the proof uses only Mathlib's polynomial expansion of
`det (1 + X • M)`.
