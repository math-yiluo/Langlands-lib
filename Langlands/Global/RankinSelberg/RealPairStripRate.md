# A common reciprocal Gamma rate for real pair denominators of compact exponent families

`RealPairStripRateStatement` takes the following data:

- a topological parameter space with a compact set `S`;
- fixed discrete data `sh`, `sh'` of lengths `n`, `m`;
- exponent maps `p`, `q` that are continuous in the parameter.

It bounds, for every closed vertical strip `u ≤ Re s ≤ v`, both

- the pair reciprocal `L`-factor of `blockList sh (p z)` and `blockList sh' (q z)`, and
- the pair reciprocal `L`-factor of their dual lists (`map dualBlock`),

by `C · exp(blockCount · π · |Im s|)`, uniformly for `z ∈ S`. Here `blockCount sh sh'` is the
total number of blocks of the pair presentation, `∑_i ∑_j |tensorShape (sh i) (sh' j)|`. It is
the same for the dual data (`blockCount_dual`). This is the real counterpart of
`ComplexPairStripRateStatement`.

## Proof

1. `norm_gammaReal_denominator_le_exp`: on every closed strip,
   `‖1/Γ_ℝ(s)‖ ≤ C exp(π |Im s|)`. Write `1/Γ_ℝ(s) = π^(s/2) · 1/Γ(s/2)`. The modulus of
   `π^(s/2)` is `π^(Re s/2)`, at most `π^(a/2) + π^(b/2)` on the strip `a ≤ Re s ≤ b`. For
   `|Im s| ≥ 2` the Library bound `norm_inv_Gamma_le_exp_of_one_le` on the halved strip gives
   `‖1/Γ(s/2)‖ ≤ C exp(π |Im s| / 2)`. The remaining compact rectangle is handled by continuity
   of the entire function. The complex block bound with the same rate is the Library's
   `norm_gammaComplex_denominator_le_exp`.
2. A private lemma `shift_rate` transfers such a rate-`π` bound to the arguments
   `s + w + κ` with a fixed `κ` and `|w| ≤ R`. It widens the strip by `R + |κ|` and absorbs the
   imaginary part of `w + κ` into a factor `exp(π (R + |κ|))`.
3. `norm_block_denominator_le`: the denominator of `blockOfParams x 0` is `1/Γ_ℝ` or `1/Γ_ℂ`,
   shifted by the parity or half the absolute weight. So it has a uniform rate-`π` bound at
   `s + w` for `|w| ≤ R`.
4. `norm_pairDenominator_le`: the exponents are bounded on the compact set `S`, so every sum
   `p z i + q z j` has norm at most a fixed `R`. By `pairDenominator_blockList` the pair
   denominator is a product of `blockCount` block factors evaluated at such shifts. Each factor
   is bounded by its constant times `exp(π |Im s|)`. Multiplying the bounds gives the rate
   `blockCount · π`.
5. `realPairStripRate`: the dual lists are again parametrized lists, with the dual data and the
   exponents `-p`, `-q` (`map_dualBlock_blockList`), and have the same block count. The larger of
   the two constants serves both bounds.

## Provenance

This is an internal analytic estimate. The continuation in the inducing exponents
(`RealPairStripReflection`) uses it to keep a common exponential rate on every strip, as
required by `compactParameterStripGrowth`. The corresponding argument is in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §8.1, pp. 53–54.
