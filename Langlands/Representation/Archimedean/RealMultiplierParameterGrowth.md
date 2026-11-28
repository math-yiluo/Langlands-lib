# Polynomial growth of real block multipliers in a parameter disk

`RealMultiplierParameterGrowthStatement` treats the generic and regularized
sequences of `RealBlockMultiplierNormalization`. Fix a nonnegative integer
`ε` and a closed complex parameter disk of radius `r > 0`. For the generic
product the disk must avoid every denominator root. For the regularized
product one specified denominator may vanish, and the disk must avoid the
remaining roots. For each product the theorem gives constants `B ≥ 0` and a
natural exponent `d` such that the `j`th parameter derivative at the center
has norm bounded by

\[
    \frac{j!\,B}{r^j}(1+m)^d
\]

at sequence index `m`, simultaneously for all `j` and `m`. The two final
corollaries give the bound with `(1 + |k|)^d` for the corresponding full
integer-mode multipliers.

## Proof

For `a = ε + 2m + 1`, the reverse triangle bound gives `|a + z| ≥ m + 1`
when `m ≥ |z|`. The numerator satisfies `|a − z| ≤ |a + z| + 2|z|`.
Choose a natural exponent `d` dominating `2|z|` throughout the compact
parameter set. By Bernoulli's inequality the norm of the ratio is at most
`((m + 2)/(m + 1))^d` for sufficiently large `m`, uniformly on that set.
The finitely many initial sequence values have a uniform bound by
continuity and compactness. Both sequences satisfy the same multiplicative
recurrence above the initial indices, taking the threshold for the
regularized sequence past the erased index. Induction telescopes the
ratio bound against `(1 + m)^d`.

The published analyticity lemmas apply on the closed disk under the stated
exclusions. Cauchy's derivative estimate on its boundary circle gives the
factor `j!/r^j` and keeps the index exponent fixed. Extension to negative
integer modes only adds a constant factor of absolute value one, while
the sequence index is at most the absolute integer mode.

The coefficient estimates follow directly from the finite-product formulas
in `RealBlockMultiplier` and `RealBlockMultiplierNormalization`. They give
polynomial mode bounds for every coefficient of the finite Taylor jets
of the rank-two crossing symbols.
