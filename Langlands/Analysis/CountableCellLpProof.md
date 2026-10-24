# Proof of the countable-cell Lp tests

`Langlands.countableCellLp` proves exactly
`Langlands.CountableCellLpStatement`, with independent universes for the
ambient measurable space and the countable index type. Its two components
are also exposed as `countableCellLpUpper` and `countableCellLpLower`.
The functions are real-valued, the measure is arbitrary, and the extended
nonnegative exponent is nonzero and finite.

## Upper test

Put `q = p.toReal`. On each cell, monotonicity of the nonnegative real power
gives `‖f x‖ₑ ^ q ≤ (b i) ^ q`. The constant majorant is measurable, so
`setLIntegral_mono` applies even when the cell itself is not measurable.
The integral of this constant is `(b i) ^ q * μ (s i)`.

The countable-union integral inequality bounds the integral over the whole
space, using the covering hypothesis, by the sum of the integrals over the
cells. Termwise comparison bounds this sum by the assumed finite weighted
sum. Finally, almost everywhere strong measurability and the nonzero finite
exponent allow Mathlib's powered-norm integral characterization of the
finite Lp seminorm to conclude `MemLp f p μ`.

## Lower test

On each measurable cell the lower bound, raised to the same nonnegative
power, bounds the constant integral by the powered-norm integral.
The sum of these inequalities is compared with the integral over the union
by the exact countable disjoint-union identity. Restriction monotonicity
bounds this union integral by the full-space integral.
The initial `MemLp` hypothesis makes that full integral finite for the given
nonzero finite exponent. Consequently the weighted lower-bound sum is finite.
No covering condition is used in this direction.

## Internal provenance and scope

This is an elementary deduction from Mathlib's Lebesgue integral, real-power
monotonicity and Lp APIs, as specified by the statement's internal provenance.
All quantities in the integral comparisons and weighted sums remain in
`ℝ≥0∞`, including any infinite bounds or measures; there is no assumption
of finite cell measure or sigma-finiteness. The final theorem pairs the two
proved clauses without further hypotheses.

The proof supplies only a measure-theory step toward the analytic tempered
exponent criterion. It establishes no Cartan cell geometry, Haar volume bound,
matrix-coefficient estimate, lattice summability or Jacquet-exponent criterion.
