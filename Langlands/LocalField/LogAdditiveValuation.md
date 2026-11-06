# A normalized negative-logarithm adapter for valuations

Author: Worker 1676.

This is an internal derived construction from Mathlib's multiplicative valuation
and real logarithm APIs. It provides the change of convention needed when a
spectral norm is to supply a real additive root-parameter valuation. It makes no
claim about root groups or building axioms.

For a real scale `c`, `negativeLogValue c r` sends `r = 0` to infinity and sends a
nonzero nonnegative real `r` to `-log(r)/c`. The multiplication formula holds for
any scale. For `c > 0`, comparison reverses exactly: the transformed value of
`a` is at most that of `b` precisely when `b ≤ a`.

`logAdditiveValuation v c hc` composes this function with any multiplicative
valuation `v : Valuation R ℝ≥0` on any ring `R`, obtaining an actual
`AddValuation R (WithTop ℝ)`. The product law follows from `Real.log_mul`, with
zero cases handled separately. The additive valuation inequality follows by
splitting the multiplicative maximum inequality and reversing the appropriate
comparison. `logAdditiveValuation_le_iff` records the exact reversal of order.

For fields, `logAdditiveValuation_of_ne_zero` states the finite formula at every
nonzero element. `logAdditiveValuation_invariant` proves invariance under any
map that preserves the original multiplicative valuation. The ring or field
universe is unrestricted. No nontriviality, discreteness, topology, completeness,
or normalization on `v` is assumed; the only scale hypothesis is `0 < c`.

This file does not choose a scale or prove agreement with a prescribed base
valuation. The actual local-field spectral specialization and its exact base
normalization require a separate construction.
