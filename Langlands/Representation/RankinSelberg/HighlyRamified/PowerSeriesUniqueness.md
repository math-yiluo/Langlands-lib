# Uniqueness of coefficients of convergent power series

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, Corollary (3.3): the interpretation of the integral as a formal Laurent
series, whose coefficients are the integrals over determinant shells, printed page 325).

- `coeff_eq_zero_of_tsum_eq_zero`: if `Σ ‖d_n‖ r^n < ∞` for some `r > 0` and
  `Σ d_n X^n = 0` for all nonzero `X` with `‖X‖ < r`, then every `d_n` is zero. The series is the
  sum of Mathlib's `FormalMultilinearSeries.ofScalars ℂ d`, which has radius at least `r`; if it
  were nonzero, `HasFPowerSeriesAt.locally_ne_zero` would give nonvanishing on a punctured
  neighbourhood of `0`.
- `coeff_eq_of_tsum_eq_monomial`: if `Σ b_n X^n = c X^k` on such a punctured disc, then
  `b_n = c` for `n = k` and `b_n = 0` otherwise.
