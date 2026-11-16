# Removing the second cusp form from the equal-rank gauge premise

This is an internal conditional reduction for the primal half of
`EqualUnfoldingGaugeStatement`. It isolates the weighted Whittaker–Schwartz
integral used in Jacquet–Shalika, *On Euler products and the classification of
automorphic forms I* (1981), §4.5, printed pp.550–551. It does not prove that
analytic input.

For a cuspidal realization `T` of rank `n = r + 1`,
`EqualWhittakerSchwartzBound F T` asserts finiteness of

`∫ ‖W(g)‖ ‖Φ(e_n g)‖ |det g|^σ dg`

on `N_n(𝔸) \ GL_n(𝔸)`, with the Library's
`whittakerQuotientMeasure`. It requires one nonnegative threshold uniform
over standard additive characters, vectors of `T`, and Schwartz–Bruhat
functions. `EqualWhittakerSchwartzStatement` quantifies this over all number
fields and all cuspidal realizations, with the compact Adele quotient
hypothesis. `EqualGaugeReductionStatement` says this statement implies the
primal gauge premise for every pair of such realizations.

The generic lemma `EqualGaugeReduction.integrable_equalKernel_of_bound`
assumes a measurable Whittaker-covariant `W`, a measurable rational-invariant
second function `φ'`, a measurable composite `Φ(e_n ·)`, and a bound
`‖φ'(g)‖ ≤ B |det g|^β`, where `B ≥ 0`. It assumes finiteness of the weighted
Whittaker–Schwartz integral at exponent `Re(s) + β`. The kernel's norm is
bounded by `B` times that nonnegative majorant. The majorant is measurable
and invariant under `N_n(𝔸)`: the generic character has norm one, and both
the last row and determinant norm are unchanged by left unipotent
multiplication. `GaugeReduction.lintegral_rationalQuotient_eq` transfers
its integral to `N_n(F) \ GL_n(𝔸)`. Rational invariance of the kernel gives a
measurable quotient function, and the finite majorant integral proves
integrability.

The specialization
`equalWhittakerGaugeIntegrable_of_schwartzBound` uses
`CuspCentralBound.exists_norm_cuspFunction_le` for `T'`. That theorem
provides a single exponent `β`, with a nonnegative constant `B` for each
vector. If the Whittaker–Schwartz threshold is `C`, the primal gauge
threshold is `max 0 (C - β)`. Thus `Re(s) + β > C`, and the generic lemma
applies. The final theorem `equalGaugeReduction` performs the universal
specialization.

The reduction follows the source's bounded-cusp-form argument while
retaining the Library's possibly nonunitary central character through the
fixed power `β`. Its proof uses published Library results and does not
require an Iwasawa decomposition or a new analytic estimate.
