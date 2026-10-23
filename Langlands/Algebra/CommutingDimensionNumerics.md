# Numerical induction step for the commuting-algebra dimension estimate

This helper implements an internal deduction supporting
Bernstein–Zelevinsky (1976), Lemma 4.10 and §4.12, printed pp.39–40,
registered as `bernstein-zelevinsky-1976-representations-gln`.

Suppose `m > 0`, `0 ≤ s ≤ m`, and `r ≥ 1`. The helper shows that the
two inequalities `D ≤ s*m` and `D ≤ (m-s)^r + m^(2*r-2)` imply `D ≤ m^r`.
All quantities are real numbers and powers with real exponents use
Mathlib's real power function.

Put `M = m^(r-1)`. Monotonicity gives `(m-s)^r ≤ (m-s)*M`, including
`s = m`. If `D > m^r = m*M`, the first inequality forces `s > M`.
The second then gives `D ≤ m*M - s*M + M² < m*M`, a contradiction.
The implemented proof expands these power identities and finishes with
ordered-ring arithmetic.

Worker 307 authored this deduction. It replaces the source's maximal
dimension function and floor calculation by a direct induction step.
This module proves no algebraic dimension estimate by itself.

The function `dimensionExponent l = 2 - 2/2^l` has value zero at
`l = 0`, is at least one for positive `l`, and satisfies
`dimensionExponent l = 2 * dimensionExponent (l+1) - 2`. These elementary
identities connect the two induction hypotheses to the numerical lemma.
