# Newton's identities for matrices

Let `M` be an `N × N` matrix over a commutative ring and let `c_j` be the coefficient of
`t^{N-j}` in its characteristic polynomial `χ`. `newton_identity` states that
`k c_k + ∑_{j<k} c_j tr(M^{k-j}) = 0` for `k ≤ N`.

The proof follows Faddeev–LeVerrier.

* `derivative_det` (Jacobi's rule, from the Leibniz formula): the derivative of a determinant
  of polynomials is the sum of the determinants with one column differentiated. Hence
  `χ' = tr adj(t - M)` (`derivative_charpoly`, via `cramer`).
* Write `Q_m` (`adjCoeff`) for the coefficient matrices of `adj(t - M)`. The identity
  `(t - M) adj(t - M) = χ` gives `Q_m = M Q_{m+1} + χ_{m+1}` and `M Q_0 + χ_0 = 0`.
  It also gives `Q_m = 0` for `m ≥ N` (a downward induction from the degree of `adj(t - M)`),
  so `Q_{N-1-k} = ∑_{j ≤ k} c_j M^{k-j}`.
* Taking traces: `tr Q_m = (m+1) χ_{m+1}` gives the identities for `k < N`, and the trace of
  `M Q_0 + χ_0 = 0` gives the case `k = N`.
