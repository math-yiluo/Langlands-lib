# Uniqueness of power series coefficients and polynomial functions

Module `Langlands.Representation.Shahidi.OpenCellPowerSeries`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `eq_zero_of_hasSum_pow`, `eq_of_hasSum_pow`: two complex power series converging to the same
  value at every nonzero point of a disc of positive radius have the same coefficients (via
  `FormalMultilinearSeries.ofScalars` and the isolated zeros theorem).
- `hasSum_nat_of_hasSum_int`: a series over `ℤ` supported on `ℕ`.
- `IsPolynomialFn F` and `IsLaurentFn F`: functions on `ℂˣ` given by a polynomial, respectively
  by a polynomial divided by a power of the variable; closure under sums, products, finite sums
  and products, integer powers of the variable (`isLaurentFn_zpow`) and evaluation of
  multivariate polynomials at polynomial coordinates (`isPolynomialFn_mvEval`).
- `IsPolynomialFn.eq_of_infinite`, `IsLaurentFn.eq_of_infinite`: such functions agreeing on an
  infinite set agree everywhere; `infinite_small_units`: for `ρ > 0`, the units of norm `< ρ` form
  an infinite set.

## Provenance

Standard complex analysis and algebra (Mathlib `HasFPowerSeriesAt.locally_ne_zero`,
`Polynomial.eq_of_infinite_eval_eq`).
