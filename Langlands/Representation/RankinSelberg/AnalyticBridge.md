# The JPSS analytic statements and the intrinsic zeta values

Worker 31 connects two published descriptions of the rational functions in
Theorem 2.7 of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), printed pages 390–391, in the setting of §2.1, printed
pages 385–386. The source is registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

- Worker 31's `LocalFactor` defines the zeta values of a pair through the
  Whittaker sets `whittakerSet` and `inverseWhittakerSet`, the union over all
  functionals. It keeps only integrals that converge absolutely on a right
  half-plane and have a rational continuation.
- Worker 11's `AnalyticStatement` defines `equalRankRationalValues` and
  `unequalRankRationalValues` for one specified pair of functionals `ℓ, ℓ'`.
  It keeps the continuations of the integrals over their coefficient models,
  with no convergence condition. It also states the analytic part of Theorem 2.7
  as propositions.

The module proves that the two sets agree under the source's hypotheses. Hence
every proof of Worker 11's analytic propositions supplies the existence
hypothesis of the conditional L-factors `equalRankLFactor` and
`unequalRankLFactor`. The content is derived; no theorem of the source is
quoted. Nothing analytic is proved: convergence, rationality and the existence
of the generator remain the hypotheses `EqualRankAnalyticConclusion`,
`UnequalRankAnalyticConclusion` and the p-adic statements built from them.

## Multiplicity one

JPSS call a representation "of Whittaker type" when it is admissible, of finite
type, and its space of functionals for the specified character is
one-dimensional (page 385). Worker 11's `IsOfWhittakerType n θ π` states the
last condition as a linear equivalence of `functionals (upperUnipotent (n + 1) F)
θ π` with `ℂ`. `exists_eq_smul_of_linearEquiv` shows that in a complex vector
space linearly equivalent to `ℂ`, every vector is a multiple of any nonzero
vector. Hence `IsOfWhittakerType.exists_ne_zero` gives a nonzero functional,
and `IsOfWhittakerType.eq_smul` shows that every functional is a multiple of any
nonzero one. Admissibility and finite type are not used.

## Equal rank

`equalRankValuesOf_coefficientModel_subset` shows that the values of
`LocalFactor`'s `equalRankValuesOf`, applied to the coefficient models of `ℓ`
and `ℓ'`, lie in `equalRankRationalValues` for `ℓ, ℓ'`: dropping the
convergence condition only enlarges the set. Both sets use the published
`equalRankIntegral` of `QuotientIntegrals`: Worker 11's set through the wrapper
`equalRankModelIntegral` of the same module, which is by definition that
integral of the two model vectors. `equalRankValuesOf_coefficientModel_eq` gives equality when every
integral over the two models converges on some right half-plane. This
hypothesis is exactly the first conjunct of `EqualRankAnalyticConclusion`.

`equalRankZetaValues_eq_rationalValues` combines this with `LocalFactor`'s
`equalRankZetaValues_eq_model`. If `π` is of Whittaker type for the standard
character, `σ` for the inverse standard character, `ℓ` and `ℓ'` are nonzero,
and the model integrals converge on right half-planes, then
`equalRankZetaValues q ψ abv μ π σ` equals `equalRankRationalValues q ψ abv μ
π σ ℓ ℓ'`. The parameters `q`, `ψ`, `abv` and `μ` are the same on both sides.

Under `EqualRankAnalyticConclusion` for `ℓ, ℓ'` and the same Whittaker-type and
nonzero hypotheses:

- `EqualRankAnalyticConclusion.zetaValues_eq` states this equality.
- `EqualRankAnalyticConclusion.hasCommonDenominator` gives the zeta values a
  common denominator, RationalZeta's `HasCommonDenominator`.
- `EqualRankAnalyticConclusion.normalizedGeneratorExists` gives
  `NormalizedGeneratorExists` for the zeta values, which is the argument
  `equalRankLFactor` requires.
- `EqualRankAnalyticConclusion.isEqualRankLPolynomial_iff` shows that `P` is the
  L-polynomial `IsEqualRankLPolynomial` exactly when it is the normalized
  generator of Worker 11's rational values.

## Unequal rank

The unequal-rank theorems are the same for the block integrals with fixed `j`
and `k`, with `π` on `GL_(n + (j + k + 1) + 1)(F)`, `σ` on `GL_(n+1)(F)`, any
measure `μ` on the left-unipotent quotient and any measure `ν` on the
`j × (n + 1)` matrices. They are `unequalRankValuesOf_coefficientModel_subset`,
`unequalRankValuesOf_coefficientModel_eq`,
`unequalRankZetaValues_eq_rationalValues`, and the four consequences of
`UnequalRankAnalyticConclusion`: `zetaValues_eq`, `hasCommonDenominator`,
`normalizedGeneratorExists` and `isUnequalRankLPolynomial_iff`. Each block
`(j, k)` is treated separately. The common generator over all blocks of fixed
ranks, Worker 11's `UnequalRankCommonGeneratorStatement`, is not used here.

## The p-adic statements

Worker 11's `EqualRankAnalyticStatement F T n` asserts
`EqualRankAnalyticConclusion` over the p-adic field `F` with topological data
`T`. It quantifies over every additive character, every quotient measure `μ`
that satisfies the published `IsCompatible` with `generalLinearHaar` and
`unipotentHaar` (assuming right invariance of the latter), every pair of
Whittaker type and every pair of nonzero functionals. The parameters are
`q = T.residueCardinality` and `abv = normalizedAbsoluteValue T`.

`EqualRankAnalyticStatement.normalizedGeneratorExists` shows that this
statement gives, with the same quantifiers but no chosen functionals,
`NormalizedGeneratorExists` for `equalRankZetaValues T.residueCardinality ψ
(normalizedAbsoluteValue T) μ π σ`. The functionals are supplied by
`IsOfWhittakerType.exists_ne_zero`. So once the statement is proved,
`equalRankLFactor` is defined for every pair of Whittaker type.
`UnequalRankAnalyticStatement.normalizedGeneratorExists` does the same for the
block `(j, k)`, with `ν` the published `rectangularMeasure` of an additive Haar
measure on `F`, as in Worker 11's statement.

The proofs reintroduce, as local instances, the topology `T.topology` and the
Borel σ-algebras on `F` and on the quotient, which the statements fix with
`letI`.

## Imports

The module imports `LocalFactor` and Worker 11's `AnalyticStatement`. All
other declarations used come from their published imports: `QuotientIntegrals`,
`Measures`, `RationalZeta`, `RationalContinuation` and the Whittaker modules.
