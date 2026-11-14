# Corank-one integrals as the zero blocks of the unequal-rank family

Module `Langlands.Representation.Conductor.SphericalCorankOneIntegrals`, namespace
`Langlands.Conductor.SphericalCorankOne`. It is an internal helper for the proof of
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`. Every result except the last
holds over an arbitrary field `F` with the stated topology and measurability instances. The last
result holds over every nonarchimedean local field. No `PadicField` is involved.

## Statements

- `corankOneIntegral_eq_unequalRankIntegralAt ψ abv μ ν W W'`: the published corank-one integral
  of `W` (rank `n+2`) and `W'` (rank `n+1`) equals the published block integral
  `unequalRankIntegralAt 0 0 rfl` with the zero-row rectangular measure
  `rectangularMeasure ν 0 (n+1)`. The equality holds for every `s`.
- `corankOneConverges_iff_unequalRankConverges ψ abv μ ν W W' s`: `CorankOneConverges` at `s` is
  equivalent to `UnequalRankConverges` for the blocks `j = k = 0` with that measure.
- `blockWeylAt_succ_eq_one`: the block Weyl representative `blockWeylAt n (n+1)` is the identity.
- `dualUnequalRankModelIntegralAt_eq_corankOneIntegral ψ abv μ ν π σ ℓ ℓ' f f'`: for model
  functions `f` of `π` (rank `n+2`) and `f'` of `σ` (rank `n+1`), the published transformed
  block integral `dualUnequalRankModelIntegralAt _ 0 0 rfl` is the corank-one integral, for the
  character `ψ.scale (-1)`, of `firstDualFunction ψ (n+1) f` and `secondDualFunction ψ n f'`.
- `corankOne_gammaFunctionalEquation`: let `F` be a nonarchimedean local field and let `G` be a
  gamma factor of `π × σ` in the published sense `IsPairGammaFactor q ψ abv ν π σ G`. Fix a
  compatible quotient measure `μ`, nonzero functionals `ℓ`, `ℓ'` and model functions `f`, `f'`.
  Then there is a scalar `ζ` with `HasModelMinusOneScalar σ ℓ' ζ` and rational functions `R`,
  `R̃`. `R` continues the corank-one integral of `f, f'` and `R̃` continues the corank-one integral
  of the two dual functions (for `ψ.scale (-1)`). Together they satisfy
  `GammaFunctionalEquation q ζ (n+1) G R R̃`.

## Proofs

- Integral: the zero-row rectangular measure is the Dirac mass (`rectangularMeasure_zero_rows`).
  The block integrand at `j = k = 0` is the corank-one integrand (`unequalRankIntegrand_zero_zero`).
  `integral_dirac` finishes.
- Convergence: the same Dirac reduction. Forward: multiply by the constant `1` on the Dirac
  factor (`Integrable.mul_prod`). Backward: integrate out the Dirac factor
  (`Integrable.integral_prod_left`). This is the argument of the published p-adic
  `UnequalRankZeroRowAssembly.zero_row_converges_iff`, which itself only assumes a field.
- Weyl element: `weylLong 1 = 1` (`RankOneGammaTwist.weylLong_one`), and the block-sum embedding
  and reindexing are monoid maps.
- Dual block: unfold `dualUnequalRankModelIntegralAt`. The Weyl translate is by `1`, so the
  translated dual function is the dual function itself. Then apply the integral identity for
  `ψ.scale (-1)`.
- Gamma functional equation: `isPairGammaFactor_of_lt` unfolds the gamma factor for ranks
  `n+1 < n+2`. Its block statement for `j = k = 0` gives `ζ` and the continuations of the block
  integral and of the transformed block integral, with the gamma equation at exponent `n+1`.
  The two identities above rewrite these as corank-one integrals.

## Provenance

The identification of the corank-one integral with the `j = 0` term of the JPSS family is JPSS
1983, Section 2 (printed pages 389–391), where the corank-one case is the case `j = 0` of the
integrals `Ψ(s; W, W'; j)`. The Lean proofs are internal.
