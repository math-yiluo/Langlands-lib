# Rapid decay of the cuspidal open-cell factor integral

This internal assembly module turns the cutoff-power factor-integral
estimate into the arbitrary-polynomial decay used for the open-cell
part of VIII.3.1.

`exists_cutoff_xi_sq_le` is a real-variable lemma. Suppose a nonnegative
function Xi has an upper bound `C eA (1 + σ)^D` on a set, the height is
nonnegative, a nonnegative multiplier `η` satisfies
`η eA² ≤ e₀²`, and `t ≥ b (1 + σ)` there for some `b > 0`.
For every real `r`, choosing `p = max(r + 2D, 0)` yields a finite
nonnegative `B` with

```text
η t^(-p) Xi² ≤ B e₀² (1 + σ)^(-r).
```

The proof squares the Xi upper bound, uses the linear cutoff bound to
replace `t^(-p)`, and compares the remaining height exponent
`2D - p` with `-r`.

`CuspidalFactorIntegralDecayBound` is the precise nonnegative
lower-integral estimate for the product of the two split-factor norms,
with right side `c e₀(a)² (1 + σ(a))^(-r)` for every real `r`.

`cuspidalFactorIntegralDecayBound_of_tail` proves it assuming the
cuspidal-factor tail bound and second-factor decay bound, Levi
`ConvolutionWeights`, right compact invariance of the Levi height, a
Levi chamber Xi upper estimate measured with the ambient conjugator
height, the inverse-radical-modulus comparison, and a linear cutoff.
It applies `lintegral_cuspidalFactors_le_of_tail` at the exponent chosen
by the real-variable lemma, with `η = δU⁻¹`, then multiplies the two
finite constants.

All analytic and geometric premises are explicit. This module does not
prove the actual Xi or constant-term estimates and does not assert the
closed actual-point VIII.3.1 statement. It removes any need to repeat
the older representative-wise tail argument when whole-Levi
constant-term estimates are available.
