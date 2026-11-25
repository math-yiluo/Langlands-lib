# The torus derivative of a principal-series function

For characters `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}`:

- `torusDeriv l t d = ∑_k (l_k i Im d_k + 2 τ_k Re d_k)` with `τ_k = t_k + (n-1)/2 - k`.
- `phase_exp`, `norm_exp_cpow`: `phase(e^w) = e^{i Im w}` and `|e^w|^{2s} = e^{2 Re(w) s}`.
- `principalSeriesCharacter_exp`: the normalized character of the Library's principal series
  at `diag(e^{s d_k})` is `exp(s · torusDeriv l t d)`.
- `fderiv_unitsExtension_diagonal_mul`: for `f` in `principalSeries ℂ n χ` and a unit `y`, the
  derivative of `unitsExtension f` at `y` in the direction `diag(d) y` is
  `torusDeriv l t d · f(y)`: differentiate `s ↦ f(exp(s diag d) y) = exp(s torusDeriv) f(y)` at
  `s = 0` (`ComplexDuality.LieInvariance.unitsExtension_diagonal_mul`).

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
