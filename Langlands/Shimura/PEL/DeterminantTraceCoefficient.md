# Extracting the trace from the actual binary determinant polynomial

This internal construction extracts a trace from a binary polynomial without choosing a degree or dividing by a rank. For any commutative ring `R`, `traceCoefficient p` evaluates the two variables of `p : MvPolynomial (Fin 2) R` at `(1, X)` in `Polynomial R`, then takes coefficient `1`.

`traceCoefficient_map` proves that extraction commutes with every coefficient ring homomorphism `R →+* S`. The proof compares the mapped polynomial evaluations using `MvPolynomial.hom_eval₂` and `MvPolynomial.eval₂_map`, checks that the two evaluation values map to `(1, X)`, and applies `Polynomial.coeff_map`. It imposes no injectivity, flatness, reducedness or characteristic hypothesis.

For an actual module basis `b : Module.Basis κ R M` with finite decidable index type and an actual endomorphism `f`, `traceCoefficient_polynomial` proves

```text
traceCoefficient (HodgeDeterminant.polynomial b ![1, f])
  = LinearMap.trace R M f.
```

The left side is the determinant polynomial constructed from the actual endomorphisms, rather than a supplied characteristic polynomial. The proof evaluates it as the determinant of `1 + X • map Polynomial.C (toMatrix b b f)`. Mathlib's `Matrix.coeff_det_one_add_X_smul_one` identifies the linear coefficient with the matrix trace, and `LinearMap.trace_eq_matrix_trace` identifies that trace with the intrinsic endomorphism trace. The basis provides the finite free presentation needed for this interpretation, including when its index type is empty.

The provenance is internal: the definitions and proofs derive a coefficient operation on the existing `HodgeDeterminant.polynomial` from polynomial evaluation, matrix determinants and Mathlib's trace theorems. No external mathematical statement or geometric comparison is assumed.
