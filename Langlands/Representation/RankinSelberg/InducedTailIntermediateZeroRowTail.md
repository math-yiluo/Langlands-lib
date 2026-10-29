# Reversed zero-row tail integrability and continuation

Supporting adapters by Worker 829 for the intermediate-rank calculation in
JPSS section 9.3, printed pages 456–457. They turn membership in the actual
zero-row unequal-rank zeta values into the tail data used by the conditional
diagonal-extension statement: an integrable quotient integrand on a right
half-plane, together with the rational continuation of its integral. These
results are internal derivations from the published Library zeta-value
definitions and from Worker 318's coefficient and character-transport
modules. They do not prove any disintegration, compute any integral or prove
the intermediate-tail span inclusion.

## Zero rectangular rows

The Library theorem `rectangularMeasure_zero_rows` rewrites the rectangular
measure with zero rows to the unit point mass at the zero matrix. With this
rewrite, the zero-row lemmas `unequalRankConverges_zero_rows_iff` and
`unequalRankIntegral_zero_rows` of `InducedTailIntermediateIntegralAssembly`
give three statements for an arbitrary quotient measure `μ`, additive Haar
measure `ν` and coefficients `W`, `W'` of ranks `n + (0 + k + 1)` and `n`:

- `unequalRankConverges_rectangular_zero_rows_iff`: `UnequalRankConverges`
  with `rectangularMeasure ν 0 (n + 1)` holds at `s` exactly when the quotient
  integrand `unequalRankIntegrand ψ abv 0 k W W' s 0` at the zero matrix is
  integrable for `μ`;
- `unequalRankIntegral_rectangular_zero_rows`: as functions of `s`, the
  iterated integral `unequalRankIntegral` with this measure equals the
  quotient integral of that integrand;
- `unequalRankContinuation_rectangular_zero_rows_iff`: the iterated integral
  has rational continuation `R` exactly when the quotient integral has
  rational continuation `R`, with the same `R`.

## Rank transport

`inverseWhittakerRankCast_trans` states that transporting an inverse
coefficient along `l = m` and then along `m = n` is the transport along the
composite equality. The proof substitutes both equalities.

## Reversed tail data

`exists_reversedTail_of_mem_scaled` works with general ranks `r` and `m`, an
equality `hm : r = m` and an equality `hk : m = n + (0 + k + 1)`. Suppose `R`
belongs to the actual zero-row zeta values
`unequalRankZetaValuesAt 0 k (hm.trans hk) q (ψ.scale (-1)) abv μ
(rectangularMeasure ν 0 (n + 1)) σ τ` at the inverse character. Membership
supplies a standard coefficient of `σ` at `ψ.scale (-1)`, an inverse
coefficient of `τ` at `ψ.scale (-1)`, a half-plane of absolute convergence
and the rational continuation `R`. The theorem then produces:

- `Wtest` in the inverse coefficient image of `hm ▸ σ` at `ψ`, namely the
  standard coefficient recast by `scaledStandardAsInverse`;
- `Wtail` in the standard coefficient image of `τ` at `ψ`, namely the inverse
  coefficient recast by `scaledInverseAsStandard`;
- a real `a` such that for `a < Re s` the function
  `unequalRankIntegrand (ψ.scale (-1)) abv 0 k
  (inverseAsScaledStandard ψ (inverseWhittakerRankCast ψ hk Wtest))
  (standardAsScaledInverse ψ Wtail) s 0` is integrable for `μ`;
- rational continuation `R` of the quotient integral of that function.

After substituting both rank equalities, the recastings are inverse to each
other and retain the underlying functions. The integrand is therefore the
original zero-row integrand, and the zero-row lemmas above convert the
convergence and continuation premises. With `q` the p-adic residue
cardinality, `abv` the normalized absolute value and `m = n + d`, this
integrand is the function `g` of `InducedTailIntermediateDiagonalExtensionSpanStatement`.

`exists_reversedTail_of_mem_compatible` gives the same conclusion for a value
at the original character `ψ`. It assumes the supplied p-adic topological
realization with Borel measurable structures, the normalized absolute value,
residue parameter `T.residueCardinality`, any additive Haar measure `ν` and a
quotient measure `μ` compatible with the Haar measures of the general linear
and unipotent groups. Worker 318's
`unequalRankZetaValuesAt_scale_neg_one_compatible`, applied with the same
compatible measure on both sides, rewrites the value set at `ψ` as the value
set at `ψ.scale (-1)`. The theorem then applies
`exists_reversedTail_of_mem_scaled`. No integral comparison or measure scalar
is assumed.

## Provenance

Internal derivation from the published Library definitions of the unequal-rank
zeta values and from Worker 318's coefficient recasting and inverse-character
transport. The motivating source is the zero-row (`j = 0`) case of the
unequal-rank integral in the registered `jpss-1983-rankin-selberg`, section
9.3, printed pages 456–457,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source does not state these adapters as separate results.
