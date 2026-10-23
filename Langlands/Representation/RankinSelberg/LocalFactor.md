# JPSS zeta-value sets and normalized L-factors

Worker 31 implements the objects named in Theorem 2.7 of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983), printed
pages 390–391, with the conventions of §2.1, printed pages 385–386. Both pages
were read directly from the original scan. The source is registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The module defines the rational functions obtained from the actual JPSS
integrals, the L-polynomial as a relation on them, and L-factors that can only
be built from a proof that the normalized generator exists. Convergence,
rationality and existence of the generator, which make up Theorem 2.7(i)–(ii),
are neither assumed nor proved here.

## Whittaker functions of a representation

JPSS §2.1, formula (3) on page 386, defines `𝒲(π; ψ)` as the set of all
functions `W(g) = λ[π(g)v]`, with `λ` a Whittaker functional and `v` a vector.
`whittakerSet ψ n π` is exactly this set, over every functional in the
published `glFunctionals ψ n π` and every vector: the union of the published
coefficient models `coefficientModel π ℓ`. No functional is chosen.
`inverseWhittakerSet` is the same set for the inverse standard character,
`𝒲(π'; ψ̄)` in the source.

JPSS state Theorem 2.7 for representations "of Whittaker type": admissible
representations of finite type whose functionals form a one-dimensional space
(page 385, condition (2)). The definitions here take any complex representation
of the actual group `GL_(n+1)(F)` and add no admissibility, smoothness or
irreducibility hypothesis. `whittakerSet_eq_coefficientModel` proves that if
every functional is a multiple of `ℓ₀`, the set equals the coefficient model of
`ℓ₀`, so in the source's setting it is the source's subspace. The proof uses
`coefficientModel_smul_le`: coefficients of `c • ℓ` are coefficients of `ℓ`.
If `π` has no nonzero functional, its Whittaker set is contained in `{0}`
(`whittakerSet_subset_zero`, `inverseWhittakerSet_subset_zero`). When moreover
`1 < q`, every zeta value below is `0` and no L-polynomial exists; see the
section on pairs without functionals. So for `1 < q` these definitions attach no
factor to such a representation. The factors from Langlands data (JPSS §§8–9)
are separate later work.

## Zeta values

`equalRankValuesOf q ψ abv μ S S'` is the set of rational functions `R` in the
spectral variable for which some `W ∈ S`, `W' ∈ S'` and Schwartz–Bruhat `Φ`
give an equal-rank integral that converges absolutely on a right half-plane
and, on a right half-plane, equals `R` evaluated at `q^(-s)`. The integral,
its convergence predicate and its measure are those of the published
`QuotientIntegrals` module. Continuation is Worker 11's published
`HasRationalContinuation` from `RationalContinuation`, so the spectral point is
its `spectralPoint q s = q^(-s)`. `unequalRankValuesOf` is the same construction
for the block integral `Ψ(s, W, W'; j)` with fixed `j` and `k`. The ranks are
`t = n + 1` and `r = n + (j + k + 1) + 1`, so `r - t = j + k + 1` and
`0 ≤ j ≤ r - t - 1` as in the theorem. Both sets are monotone in `S` and `S'`.

`equalRankZetaValues` and `unequalRankZetaValues` apply this to the Whittaker
sets of `(π, π')`. `equalRankModel_mem_zetaValues` and its unequal analogue show
that a convergent and continued integral of the published model-integral
wrappers is a zeta value. Under multiplicity one for both members,
`equalRankZetaValues_eq_model` and `unequalRankZetaValues_eq_model` identify the
zeta values with those of the coefficient models of spanning functionals.

All parameters stay explicit. `q` is a natural number, and in the p-adic case
it should be the residue field cardinality, as on JPSS page 376. The definitions
accept every `q`, but only `1 < q` gives a usable spectral variable. For
`q = 0` and `q = 1`, `spectralPoint q s` takes at most two values, and
uniqueness of rational continuation can fail. At `q = 1` the nonzero `X - 1`
continues the zero function (`exists_ne_zero_hasRationalContinuation_one`).
Statements that rely on uniqueness of continuation therefore assume `1 < q`, as
the published `HasRationalContinuation.unique` does. `abv` is an
`AbsoluteValue F ℝ`, and
in the p-adic case it should be the normalized absolute value with
`|ϖ| = q⁻¹`. The module does not link `q` and `abv`. The Library's
`LocalField/Normalization` supplies `residueCardinality` and the unbundled
function `normalizedAbs`, but exports no bundled `AbsoluteValue`, so `abv` is
taken as an argument. `μ` is any measure on the
published left-unipotent quotient and `ν` any measure on the `j × (n + 1)`
matrices. For every natural `n` and nonarchimedean local field `F`, with Borel
structures on the ambient group, subgroup and quotient, the published
[UnipotentQuotient](UnipotentQuotient.md) constructs `unipotentQuotientHaar`
on `N_(n+1) \ GL_(n+1)(F)`. It proves
`unipotentQuotientHaar_isCompatible` and
`unipotent_compatibleMeasureExists` for the normalized `generalLinearHaar`
and `unipotentHaar`. Its `unipotentQuotientHaar_unique` proves exact equality
with this measure for any compatible measure with those same fixed Haar
normalizations. The p-adic companion
[QuotientHaarExistence](QuotientHaarExistence.md) proves the exact
`QuotientHaarExistenceStatement F T n` for every supplied `TopologicalData T`.
These constructions leave the arbitrary measure parameters here unchanged.
Convergence, rationality and existence of a normalized generator remain
separate analytic obligations.

## L-polynomials and L-factors

Theorem 2.7(ii) states that the integrals span a fractional ideal
`ℂ[q^(-s), q^s] L(s, π × π')` with `L = P(q^(-s))⁻¹`, `P ∈ ℂ[X]`, `P(0) = 1`.
`IsEqualRankLPolynomial q ψ abv μ π π' P` is the published
`IsNormalizedGenerator` relation of `RationalZeta` on the zeta values: `P` has
constant coefficient `1`, and the Laurent span of the values is generated by
`1 / P`. `IsUnequalRankLPolynomial` is the same for fixed `j` and `k`. The span
is RationalZeta's `zetaSpan`, the span over Laurent polynomials. In the source
the complex span of the integrals is itself the fractional ideal. The Laurent
span contains the complex span, and the two agree once the complex span is
shown to be a Laurent module. That agreement is part of the theorem and is not
used here.

`equalRankLFactor` and `unequalRankLFactor` are `normalizedFactor` of the
corresponding values. They take a proof of `NormalizedGeneratorExists` as an
argument, so they cannot be formed before the existence theorem is proved.
`equalRankLFactor_eq` and `unequalRankLFactor_eq` show that the factor is
`1 / P` for every `P` satisfying the relation, by RationalZeta's uniqueness.

JPSS assert that the unequal-rank factor does not depend on `j`. Here every
`(j, k)` has its own relation and factor. Independence of `j`, of the additive
character, and of `μ` up to a Haar normalization constant are separate theorem
obligations, as are convergence and rationality.

## Pairs without functionals

This section is derived, not quoted. It makes precise the remark above about
representations with no nonzero functional. `whittakerSet_subset_zero` and
`inverseWhittakerSet_subset_zero` show that if every functional of `π` is `0`,
its Whittaker set is contained in `{0}`. `equalRankIntegral_eq_zero` and
`unequalRankIntegral_eq_zero` show that the integral vanishes for every `s`
when one of its two Whittaker functions is `0`. The proof evaluates the
integrand on representatives with the published `equalRankIntegrand_mk` and
`unequalRankIntegrand_mk`.

`eq_zero_of_hasRationalContinuation_zero` shows that, for `1 < q`, the only
continuation of the zero function is `0`. It applies the published
`HasRationalContinuation.unique` to `0`, whose denominator is `1`.
`exists_ne_zero_hasRationalContinuation_one` shows that the hypothesis cannot
be dropped: at `q = 1` every spectral point is `1`, so `X - 1` continues the
zero function. This is Reviewer 232's counterexample to the unqualified
statement in an earlier version of this module.

With `1 < q`, `equalRankValuesOf_subset_zero` and
`unequalRankValuesOf_subset_zero` give values in `{0}` when one of the two sets
of functions is contained in `{0}`. `equalRankZetaValues_subset_zero` and
`unequalRankZetaValues_subset_zero` apply this when every functional of `π`, or
every functional of `π'`, is `0`.

`not_isNormalizedGenerator_of_subset_zero` shows that values contained in `{0}`
have no normalized generator: their Laurent span is `⊥`, but a generator `P`
puts the nonzero `1 / P` in the span. `not_normalizedGeneratorExists_of_subset_zero`
restates this for `NormalizedGeneratorExists`. Hence, for `1 < q`,
`not_normalizedGeneratorExists_equalRank` and
`not_normalizedGeneratorExists_unequalRank` show that the existence hypothesis
of `equalRankLFactor` and `unequalRankLFactor` fails for such a pair. The
character-pair values of a later section are not covered by a separate lemma.

## Independence of the measure normalization

`hasRationalContinuation_const_mul` shows that multiplying a function by a
constant `c` multiplies its continuation by the constant rational function `c`.
The proof bounds the denominator of the product by Mathlib's `denom_mul_dvd`
and evaluates the product with `RatFunc.eval_mul`. `zetaSpan_eq_of_const_mul`
shows that two value sets that are nonzero constant multiples of each other
have the same Laurent span. `isNormalizedGenerator_congr` and
`normalizedGeneratorExists_congr` then depend only on the span.

For a constant `c` in `ℝ≥0∞` with `c ≠ 0` and `c ≠ ∞`, replacing `μ` by `c • μ`
leaves the convergence predicate unchanged (Mathlib's `integrable_smul_measure`)
and multiplies every integral by `c.toReal` (`integral_smul_measure`). Hence
`zetaSpan_equalRankValuesOf_smul_measure` and
`zetaSpan_unequalRankValuesOf_smul_measure` give equal spans, and
`isEqualRankLPolynomial_smul_measure`, `isUnequalRankLPolynomial_smul_measure`
and `isCharacterLPolynomial_smul_measure` show that the L-polynomial does not
depend on the normalization of `μ`. The unequal-rank version assumes `SFinite ν`
for Mathlib's `Measure.prod_smul_left`. This covers positive rescaling only.
That the compatible quotient measure is unique up to such a constant is not
proved here.

## Character twists and the standard factor

`rankOneCharacter χ` is the published `characterRepresentation` of Worker 4's
`Twist/Definitions`, applied to `χ ∘ det` on `GL_1`; it acts on `ℂ`. JPSS note
on page 386 that for rank one, `𝒲(π; ψ) = ℂπ`. Here the inverse Whittaker set
of this representation consists of the multiples of `χ ∘ det`, since the
unipotent subgroup is trivial.

`characterZetaValues q ψ abv μ χ m π` are the zeta values of `π × χ` for `π`
on `GL_(m+1)`. For `m = 0` they are the equal-rank values on `GL_1 × GL_1`, the
Tate integrals `∫ W(a) χ(a) Φ(a) |a|^s d^×a`. For `m + 1` they are the
unequal-rank values with `n = 0`, `j = 0` and `k = m`, namely
`∫ W(diag(a, 1_(m+1))) χ(a) |a|^(s - (m+1)/2) d^×a`. The zero-dimensional
rectangular variable then carries the unit point mass, as in the published
`unequalRankIntegral_zero_zero`. The σ-algebra on that one-point space is `⊤`,
which is its only σ-algebra. The unequal family writes the larger rank as
`0 + (0 + m + 1) + 1`, so `π` is transported along `characterPairRank m`. That
map is the published `GeneralLinear.reindex` of the identity relabelling
`finCongr`, which keeps every index value; the definitions involve no cast.
That the transported representation has the Whittaker functions of `π`, read
through the same relabelling, is clear from this description but is not stated
as a theorem here.

`IsCharacterLPolynomial` and `characterLFactor` are the corresponding relation
and conditional factor. `standardLFactor` is `characterLFactor` with `χ = 1`.
So the standard factor here is by definition the Rankin–Selberg factor
`L(s, π × 1)`. Its agreement with the Godement–Jacquet standard L-factor, or
with Tate's factor in rank one, is not asserted.

## Dual pairs

The functional equation, Theorem 2.7(iii), relates the pair `(π, π')` to
`(π^ι, (π')^ι)`, where `π^ι(g) = π(g^ι)` and `g^ι` is the transpose inverse
(page 385). By page 386, formula (4), `W̃(g) = W(w_r g^ι)` lies in
`𝒲(π^ι; ψ̄)`. `dualEqualRankZetaValues` and `dualUnequalRankZetaValues` are the
zeta values of the published `inverseTransposePullback` of both members, with
base character `ψ.scale (-1)` from the published `CharacterTransport`, which is
`ψ̄`. The measures and `(j, k)` stay the same.

These definitions need `IsTopologicalRing F` because `ψ.scale` does.
The proofs below use that the standard character of `ψ.scale (-1)` is the
inverse standard character of `ψ`. This is checked pointwise from the published
`scaledStandardCharacter_neg_one` inside each proof. No public lemma is
declared, because Worker 11's published `FunctionalEquationStatement` declares
it under the names `standardCharacter_scale` and
`standardCharacter_scale_neg_one` in the same namespace.
`functionalsCongr` moves a functional between equal characters without changing
it. With these, `dualFunction_mem_whittakerSet` proves the source's statement
that `W ↦ W̃` maps `𝒲(π; ψ)` into `𝒲(π^ι; ψ̄)`.
`dualFunction_mem_inverseWhittakerSet` proves that it maps `𝒲(π'; ψ̄)` into
`𝒲((π')^ι; ψ)`. Both use the published `dualFunctional` and
`dualFunction_coefficient` of `DualTransform`.

In the unequal-rank equation (2) of page 391, the dual integral has index
`k = r - t - 1 - j` in place of `j`. That instance is
`dualUnequalRankZetaValues` with `j` and `k` exchanged, after `π` is transported
along `n + (j + k + 1) + 1 = n + (k + j + 1) + 1`; by the source's independence
of `j` it gives the same factor. JPSS also identify `π^ι` with the contragredient
for irreducible `π` (page 386); that identification is not made here. The
epsilon factor is not defined in this module. It is to be built on Worker 11's
functional-equation relations, a separate later module.
