# Schwartz averages of linear pullbacks

`schwartzLinearAverage` integrates `κ(y) Φ(L_y x)` when `Φ` is
Schwartz, `κ` is integrable and the continuous family `L` has
uniform upper and lower norm bounds. The domains and targets of
the maps may differ.

The chain rule bounds each iterated derivative of `Φ ∘ L_y`
by the ambient derivative times the corresponding power of the
operator norm. The lower norm bound transfers each Schwartz decay
estimate to the pullback. The pointwise estimate is available as
`norm_pow_mul_linearPullbackDerivative_le`. Multiplying by the integrable norm of
the weight gives uniform domination for differentiation under the
integral. The integrated Taylor coefficients provide both smoothness
and the decay bounds for the resulting Schwartz function.
