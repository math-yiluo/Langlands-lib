# The spherical majorant on the opposite radical chart

Lean module: `Langlands.Global.RankinSelberg.RealSlotOuter`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `alpha`, `bpart` and `kpart` are
the Iwasawa coordinates of `RealIwasawa`; `GramFormula.gram l A` is the Gram determinant of the rows
`l, …, N - 1` of `A`; `CoordC`, `lowerC` and the chart theorem `gen` are from
`RealLeviChartIntegrable`, and `lowerCGL` from `RealLeviTwoBlock`.

## The spherical function

- `spherical c g = exp(Σ_i c_i α_i(g))`, with `α = alpha g` the logarithmic diagonal of the Iwasawa
  decomposition of `g`. `spherical_pos`, `continuous_spherical`; `spherical_mul_unitary`: it is
  right `O(N)`-invariant; `spherical_torus_mul`: `spherical c (torus y · g) = exp(Σ c_i y_i) ·
  spherical c g`.

## Gram determinants

- `gram_eq_exp_alpha`: `gram l g = exp(2 Σ_{i ≥ l} α_i(g))`, from `g = b k` with `b` upper triangular
  with positive diagonal (`GramFormula.gram_mul`).
- `gramExponent c l` is `c_0/2` for `l = 0` and `(c_l - c_{l-1})/2` otherwise; `sum_gramExponent`
  inverts it. `spherical_eq_prod_gram`: `spherical c g = ∏_l gram l g ^ gramExponent c l`.

## The opposite radical chart

- `integrable_spherical_lowerCGL`: let `μ : Fin N → ℕ` be a monotone block function. If
  `c_{k+1} ≤ c_k - 1` for all `k`, with strict inequality when `μ_k < μ_{k+1}`, then
  `X ↦ spherical c (lowerCGL hμ X)` is integrable on the chart of the opposite unipotent radical of
  the parabolic subgroup of the blocks of `μ`. The spherical function is the product of Gram powers
  (`spherical_eq_prod_gram`), and the chart theorem `gen` of `RealLeviChartIntegrable` gives the
  finiteness of the lower integral with the exponents `γ_l = gramExponent c l`, whose conditions
  are the two hypotheses.
