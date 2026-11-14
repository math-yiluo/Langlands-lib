# Exponential bounds for the values of the spherical Whittaker function

Author: Worker 5220. Internal helper module for the proof of
`Langlands.Conductor.SphericalCorankOneConvergenceStatement`; it introduces no
statement.

## Results

- `norm_multiset_prod_map_le`: a product over a multiset of values of norm at most
  `M ≥ 0` has norm at most `M^card`.
- `norm_eval_hsymm_le`: for `x : Fin m → ℂ` with `‖x_i‖ ≤ M`,
  `‖h_k(x)‖ ≤ 2^(m+k) M^k`, where `h_k = MvPolynomial.hsymm`: it is a sum over
  `Sym (Fin m) k` of monomials of degree `k`, and
  `card (Sym (Fin m) k) = (m+k-1).choose k ≤ 2^(m+k)`.
- `norm_eval_completeSymm_le`: the same for the published `completeSymm` with an
  integral index at most `N` (it vanishes for negative indices), with `M ≥ 1`.
- `exists_satakeSchur_bound`: for `q ≥ 1` and `x : Fin (n+1) → ℂˣ` there are
  `C > 0`, `B ≥ 1` with
  `‖halfModulus q λ * satakeSchur x λ‖ ≤ C B^(∑ |λ_i|)` for every `λ`. The Schur
  value is `(∏ x_i)^(λ_last)` times the Jacobi–Trudi determinant of the published
  `jacobiTrudi` (bounded by Mathlib's `Matrix.det_le` with the norm as absolute
  value), and `‖halfModulus q λ‖ ≤ (√q)^((n+1) ∑ |λ_i|)`.

By the published `sphericalWhittaker_torus`, these are the torus values of the
spherical Whittaker function `W(x; ψ̄)`.

## Provenance

Elementary (internal): Jacobi–Trudi expression of the Schur polynomial and a
count of monomials of the complete homogeneous symmetric polynomials.
