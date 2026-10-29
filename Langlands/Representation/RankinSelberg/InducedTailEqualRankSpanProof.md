# Equal-tail-rank induced Laurent-span inclusion

Author: Worker 646. Worker 53 identified the compatible-measure uniqueness
route used in the assembly.

`Langlands.RankinSelberg.inducedTailEqualRankSpan.{uF,uV₁,uV₂,uW}` proves exactly
the closed published
[`InducedTailEqualRankSpanStatement`](InducedTailSpanStatement.md).
It retains the independent field, two block-carrier and test-carrier universes.
The theorem applies the assembly `inducedTailEqualRankSpan_of_extension` to the
published proof
[`Whittaker.twoBlockWhittakerExtension`](../Whittaker/TwoBlockExtensionProof.md).
Thus the extension proposition is fully discharged in the closed theorem.

The internal helper `halfModulus_weight` uses positivity of the absolute value
of the determinant of an invertible matrix, identifies a real power with a
complex power, and adds the exponents. The positive half-modulus cancels the
negative spectral shift.

Given an actual coefficient restriction formula, `integrand_eq` descends the
resulting pointwise equality to the left-unipotent quotient.
`converges` pulls integrability back along the first projection of the product
with the unit Dirac measure on zero-row matrices. `integral_eq` then identifies
the iterated scalar integral with the equal-rank integral. The convergence
claim is proved separately from equality of total Bochner integrals.

The helper `reindex_finCongr_self` removes a reflexive rank transport.
`reindex_appendIdentity_congr` compares two identity-block embeddings after
entry-preserving rank transport when their block sizes are equal. It follows
by substituting the block-size equality and proof irrelevance. These helpers
handle natural-number arithmetic without changing matrix coordinates.
`value_mem` transfers an actual rational zeta value, including its coefficient
memberships and convergence on a right half-plane. It applies the published
`RationalContinuationLinear.continuation_of_eq_on_right` to the exact integral
equality. No existence theorem for continuations or L-polynomials is needed.

In the assembly the equal-rank hypothesis gives `t = b`. The
published `unipotentQuotientHaar_unique` identifies the independently supplied
compatible quotient measures exactly, since both use the same normalized
ambient and unipotent Haar measures at rank `b + 1`. Thus the measure scalar is
one. The actual rectangular product measure with zero rows becomes the unit
Dirac measure by `rectangularMeasure_zero_rows`. Each tail zeta value supplies
`W₂`, `W'`, `Φ`, a half-plane of convergence and a rational continuation. The
extension theorem supplies `Wfull` in the actual coefficient set of the
literal ULift-conjugated normalized induction. Its factor
`|det g|^((a+1)/2)` cancels the full integral's shift. The value-membership
helper and `zetaSpan_mono` give the inclusion.

All four independent universes are retained. The closed theorem preserves
every quantified input in the target, including arbitrary Whittaker-type
representations, all Schwartz row tests, the supplied self-dual Haar measure,
and the independent compatible quotient measures. The integrability transfer
uses the actual product with the finite unit Dirac measure. It does not infer
convergence from an equality of total integrals.

These are derived algebraic and measure-theoretic steps in the equal-rank
calculation of JPSS section 9.3, printed page 455. The original extension formula
is Proposition 9.1, printed pages 452–454. The registered source is
`jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original rendered pages and published statement documentation were consulted;
the previous source audit found no source-specific erratum in the checked
project locations.

The construction uses the imported extension proof and the published
compatible-measure uniqueness, zero-row measure and rational-continuation
transport theorems. These are internal derived steps implementing the stated
equal-rank comparison. The target pair and its imported pairs are preserved.
