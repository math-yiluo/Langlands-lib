# The spherical and regularized vectors along the chart `J(x, 1)`

Lean module: `Langlands.Representation.Archimedean.RealSphericalChart`, namespace
`Langlands.Archimedean.RealSphericalChart`. It imports `RealSphericalReach` and
`ChartIwasawaPower`, and it is part of the proof of `RealSphericalCyclicStatement`.

Setting: `χ` is a signed power with exponents `e` and `χ_l(−1) = 1` for every `l`, on
`GL_{m+1}(ℝ)`. `chartGL x = J(x, 1)` is the identity matrix with last row replaced by
`(x, 1)`, and `iotaGL k = diag(k, 1)`. `partialSq x l = r_l(x) = 1 + ∑_{j<l} x_j²`, and
`partialSqProd d c x = r_m(x)^c ∏_{l<m} r_{l+1}(x)^{d_l}` (Library, `PartialSqIntegral`).
`T₀ = signVector (m+1) e 0 0` is the spherical vector (`1` on `O(m+1)`), and
`H = signVector (m+1) e 0 (bump 0 m 1)` is the regularized vector (`κ_{mm}²` on `O(m+1)`).

## Definitions

- `IsWeaklyDominant e m`: `Re e_{l+1} ≤ Re e_l` for every `l < m`. These are weakly
  decreasing real parts of `e_0, …, e_m`. It is the closed-chamber counterpart of the
  Library's `IsStrictlyDominant`.
- `chartDiff e l = (e_{l+1} − e_l − 1)/2` for `l < m`. Its real part is the Library's
  `chartExponent e l` (`chartDiff_re`).

## Results

- `spherical_chart`: for `κ ∈ O(m+1)`,
  `T₀(J(x,1) κ) = ∏_{l<m} r_{l+1}(x)^{chartDiff e l}`.
  Proof. Write `J(x,1) = a u k` (Iwasawa). By the principal-series property,
  `T₀(J(x,1)κ) = (χδ^{1/2})(a) · T₀(kκ)` and `T₀(kκ) = 1`. The character value is a product of
  `|a_l|^{t_l}` (`principalSeriesCharacter_mul_prod_zpow` with `I = ∅`, `σ = 1`). The Library
  lemma `ChartIwasawaPower.prod_abs_cpow_chart` evaluates that product along the chart as
  `∏ r_{l+1}^{(t_{l+1} − t_l)/2}`, and the exponent here is `chartDiff e l`.
- `regularized_chart`: for `k ∈ O(m)`,
  `H(J(x,1) ι(k)) = partialSqProd (chartDiff e) (−1) x`.
  Proof. `H = qFun · T₀` (`JacquetNonvanishing.signVector_bump`), and
  `qFun(J(x,1) ι(k)) = (1 + |x|²)^{−1} = r_m(x)^{−1}` (`qFun_chart`, `partialSq_last`).
- `norm_partialSqProd_chartDiff`: the norm of this chart function is
  `r_m^{−1} ∏ r_{l+1}^{chartExponent e l}`.
- `tailCondition_chartDiff`: if `IsWeaklyDominant e m`, then
  `TailCondition (chartDiff e) (−1)`. Each term `Re chartDiff_l + 1/2 = (Re e_{l+1} − Re e_l)/2`
  is `≤ 0`, so each tail sum is `≤ −1 < 0`.
- `integral_regularized_ne_zero`: under `IsWeaklyDominant e m`, the chart function
  `partialSqProd (chartDiff e) (−1)` is integrable on `ℝ^m` with nonzero integral. This is the
  Library's `PartialSqIntegral.integrable_and_integral_ne_zero`.
- `jacquetStep_regularized`: for `k ∈ O(m)`, the partial Jacquet integral
  `(T H)(k) = ∫ H(J(x,1) ι(k)) dx` equals `∫ partialSqProd (chartDiff e) (−1)`, independently
  of `k`.

## Provenance

The module was written for this project, following the chart computations of
`JacquetNonvanishing` and `ChartIwasawaPower`. The only new point is the exponent `c = −1`
contributed by the factor `qFun`. It makes the tail condition hold on the closed chamber, where
the chart function of `T₀` itself (`c = 0`) can fail to be integrable.
