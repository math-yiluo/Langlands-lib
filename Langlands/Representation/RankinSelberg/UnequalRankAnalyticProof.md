# JPSS unequal-rank convergence, rationality and normalized generators

Author: Worker 329.

`Langlands.RankinSelberg.unequalRankAnalytic` proves exactly the published
`UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k`. For every prime, p-adic
field `F`, supplied topological data `T`, and natural numbers `n,j,k`, it
proves all four clauses for the actual coefficient-model integrals: absolute
convergence on a right half-plane, rational continuation, a common nonzero
Laurent denominator for the entire rational-value set, and existence of a
normalized reciprocal-polynomial generator of its Laurent span. The theorem
has no additional analytic or representation-theoretic premises.

The field and the two representation carriers retain independent universes.
The full admissible, finitely generated Whittaker-type scope, specified nonzero
functionals, every compatible quotient measure and every supplied additive
Haar measure are those of the unchanged target. The large and small ranks are
`n + (j + k + 1) + 1` and `n + 1`; the positive gap is `j+k+1`. All natural
parameters are included, in particular `n=0`, `j=0`, `k=0` and the corank-one
case `j=k=0`. The determinant exponent remains `s-(j+k+1)/2`, and the actual
rectangular integral is taken before the quotient integral. The half-plane
bound may depend on the coefficient pair.

The proof first transfers the published zero-row analytics at `(0,j+k)`
through a compact rectangular expansion within the same coefficient model.
It then applies the published unit-span theorem and algebraic normalization
to the resulting value set. Independence of the generator from the block is
the separate `UnequalRankCommonGeneratorStatement`; this theorem proves the
four clauses for each fixed block.

The continuation and Laurent-span helpers are imported from the published `Langlands.Representation.RankinSelberg.RationalContinuationLinearProof`, in namespace `Langlands.RankinSelberg.RationalContinuationLinear`. Worker 64 extracted the addition, finite-sum, finite-linear-combination, half-plane-transfer and span-membership arguments from Worker 329's earlier draft and added fixed-denominator closure. This module uses that shared implementation and contains no duplicate definitions of those helpers. Its `commonDenominator_of_mem_span` retains the specified common denominator through span induction.

`integrable_separated_sum` combines Mathlib's integrability of products of integrable factors on a product measure with closure under finite sums. Only the inner measure requires the stated SFinite instance. `integral_separated_sum` integrates the second variable first, preserving the nested integral order in the JPSS definition; finite sum linearity and scalar linearity produce the complex constants. It does not replace a nonintegrable Bochner integral by an asserted formal expression.

These are derived elementary analysis and algebra supporting the reduction described in JPSS, *Rankin–Selberg Convolutions* (1983), pp.393–394, especially equation (7), registered source `jpss-1983-rankin-selberg`, SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. They are not separate source theorem transcriptions.

`unequalRankMatrix_at_zero` proves that zero rectangular entries give precisely `appendIdentity`. `integrand_of_finite_expansion` then descends the assumed coefficient identity to the actual left-unipotent quotient by quotient induction. It retains the gap `j+k+1` and exponent `s-(j+k+1)/2`. `converges_of_finite_expansion` and `integral_of_finite_expansion` specialize the separated-factor lemmas to these functions; the latter retains rectangular integration first.

`diagonal_integrand_eq_zero_rows` identifies the zero rectangular evaluation in block `(j,k)` with the zero-row block `(0,j+k)`. Its private transport lemma proves compatibility of coefficient evaluation with the dependent natural-number rank casts. The shared `UnequalRankZeroRowAssembly.zero_row_converges_iff` and
`UnequalRankZeroRowAssembly.zero_row_integral_eq` are reused from
`UnequalRankZeroRowAnalyticProof`, where their unchanged proofs are now
public. They use the published identification of the actual zero-row product Haar measure with unit Dirac mass. The convergence equivalence uses integrability of an inner integral in one direction and multiplication by the constant integrable function one in the other. It needs no SFinite assumption on the quotient measure.

`finite_common_bound` chooses a single right-half-plane bound for a finite family by summing the absolute values of the individual bounds. It also covers the empty family. The subsequent `converges_on_right_of_finite_expansion` and `continuation_of_finite_expansion` apply this bound to actual block integrals. `continuation_mem_span_of_finite_expansion` uses uniqueness of continuation for `q > 1` to place any continuation of that block integral in the Laurent span of the diagonal continuations. This is what lets a denominator uniform over the diagonal family remain uniform over all coefficient-dependent finite expansions.

`analytic_of_finite_expansion` assembles the first three analytic clauses for actual coefficient models with independent field and representation-carrier universes. Its explicit premises are an integrable finite expansion of each larger coefficient into coefficients of the same model, right-half-plane integrability of every diagonal pair, a rational continuation for every diagonal pair in a specified set `values`, and a common denominator for that set. The rectangular measure must be SFinite. Its conclusion is actual product-measure convergence for each pair, actual rational continuation for each pair, and a common denominator for the entire `unequalRankRationalValues` set. It proves this conditional transfer only; it does not establish its analytic or representation-theoretic premises.

`rectangular_schwartz_integrable` uses continuity and compact support under the actual rectangular Haar product. `padic_rectangular_schwartz_integrable` specializes it to the arbitrary supplied p-adic topology and Haar input in the parent target, using the published second-countability and sigma-compactness lemmas from `PadicScalarHaarScalingProof`. No additive Haar normalization is imposed.

`diagonal_analytic_of_zero_row` now supplies the full coefficient-model connection. Three private equality transports carry the representation, its specified functional, and its coefficient together from gap `j+k+1` to `0+(j+k)+1`. Equality elimination proves evaluation at the diagonal inclusion is unchanged. Quotient induction then identifies the actual diagonal integrands, and function extensionality makes that identity usable under `Integrable`. The theorem assumes the first three analytic clauses for the actual zero-row block on those transported models and produces the convergence, continuation, value-set membership and common-denominator hypotheses required by `analytic_of_finite_expansion`. The continuation step uses an equality of the actual nested integral functions. This is internal type transport, derived by equality elimination rather than a separate assertion attributed to JPSS. The final theorem supplies its analytic input from the published zero-row proof.

`unequalRankAnalytic_of_prerequisites` proves a conditional implication to the complete `UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k`. The only additional premises are `UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j+k)` and `UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k`. This intermediate theorem retains independent field and representation universes, every natural rank parameter, the supplied topology, every compatible quotient measure and the supplied additive Haar measure. The final theorem discharges both premises with published proofs.

The assembly transports the larger representation, its Whittaker type, and its specified nonzero functional along `0+(j+k)+1 = j+k+1`. Two private lemmas justify preservation of Whittaker type and nonvanishing by equality elimination. It instantiates the zero-row premise with these transported data, then `diagonal_analytic_of_zero_row` supplies all three diagonal hypotheses. For every coefficient, the published `Langlands.RankinSelberg.unequalRankCompactSupport` by Worker 358 supplies one compact rectangular set uniformly over the smaller general linear group. This theorem combines published smooth simple-root support with geometric Iwasawa support through actual coefficient equivariance; its paired Markdown explains that internal route to the support ingredient on JPSS p.393. The resulting support conclusion feeds the published `Langlands.RankinSelberg.unequalRankFiniteExpansion` by Worker 108. Its Schwartz functions are integrable for the original rectangular product Haar measure by `padic_rectangular_schwartz_integrable`. The previous finite-expansion transfer now gives convergence, rationality, and a common denominator for the whole block family. Finally, the published `Langlands.RankinSelberg.normalizedGeneratorExistence` by Worker 64 combines that denominator with the unit-span premise to prove the fourth clause. These published modules are reused by import; no unpublished peer proof is copied.

`unequalRankAnalytic_of_zero_row` discharges the unit-span premise of that general assembly with the published `Langlands.RankinSelberg.unequalRankUnitSpan.{uF,uV,uW}` by Worker 356, imported from `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof`. Its sole additional premise is now `UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j+k)`. The imported proof combines the compact mirabolic unit test, canonical Kirillov lifting into the specified coefficient model, and pointwise comparison of the actual block integrals to obtain unit membership in the Laurent span. It preserves the arbitrary supplied topology, measures, all rank parameters and the full Whittaker-type scope. This module reuses that result by import.

Finally, `unequalRankAnalytic` supplies
`Langlands.RankinSelberg.unequalRankZeroRowAnalytic.{uF,uV,uW} F T n (j+k)`
to `unequalRankAnalytic_of_zero_row`. The imported proof by Worker 331, with
contributions from Workers 329 and 64, combines the full Whittaker-type torus
asymptotics, compact root expansion, finite-function Mellin analysis and
quotient Iwasawa integration. It proves all three analytic conclusions with
one denominator uniform across the actual coefficient pairs, in precisely
the supplied topology and measures. Its zero-row rectangular product measure
is the unit Dirac mass. This module imports that published proof by Lean name;
it introduces no additional hypothesis in the final theorem.

All supporting results are published Library imports. In particular,
`Langlands.whittakerTypeKirillov` is used through the unit-span proof rather
than being assumed from a task assignment. The public conditional helpers
expose intermediate transfer steps; the closing theorem has only the
field, topology and rank binders of the named statement.

## Source and implementation provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.1, pp.385–386, gives the Whittaker-type scope; Section 2.4,
pp.387–388, defines the integrals; Theorem 2.7(i)–(ii), pp.390–391, states
convergence, rationality and the normalized generator. The unequal-rank
reduction on pp.393–394 uses compact rectangular support to reduce the
integral to finitely many diagonal integrals, with display (7) on p.394
retaining the full gap-dependent determinant exponent. The preceding torus
argument then gives convergence and a fixed denominator. These original
passages were read for this implementation.

The separated-factor lemmas, finite common bound and dependent rank
transports are derived analysis and type transport for the Library's actual
integrals. Rational-continuation uniqueness is used only with
`T.residueCardinality_gt_one`. The common denominator is transported through
the Laurent span of all diagonal continuations, so it applies to every
continuation of every block coefficient pair. The fourth clause uses the
separate published unit-span construction and normalized-generator algebra;
it does not follow from bounded denominators alone. The imported modules'
paired Markdown documents their own source arguments and contributors.
Only the new proof pair is supplied; the target and its imports are unchanged.
