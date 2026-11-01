# Constructed p-adic pair L-polynomials and L-factors

Author: Worker 31.

`Langlands.RankinSelberg.padicPairLPolynomial` and `padicPairLFactor`
construct the normalized polynomial and an actual unit in `RatFunc ℂ`
for full Whittaker-type pairs on `GL_(r+1)` and `GL_(n+1)` with `n ≤ r`.
Their existence follows from the published equal-rank and unequal-rank
analytic theorems and the published unequal-rank common-generator theorem.
The constructors have no analytic-existence or quotient-measure premise.
The supplied additive Haar measure remains an argument.

## Domain and normalizations

The supplied-data API quantifies over every `PadicField.{uF} p`, supplied
`F.TopologicalData`, and natural `n,r`. The field and the two complex
representation carriers have independent universes `uF,uV,uW`. Each
exported declaration installs the supplied topology, valuation relation,
local-field and second-countability instances, and the relevant Borel
structures through explicit `letI` telescopes.

The first representation has the published `IsOfWhittakerType` property for
`standardCharacter ψ r`, and the second has that property for
`inverseStandardCharacter ψ n`. This means admissibility, finite generation
over the group algebra, and a one-dimensional entire Whittaker-functional
space. Irreducibility is not required in the supplied-data API. The
character `ψ` is a `UnitaryAdditiveCharacter`, which already includes
nontriviality. The polynomial relation uses every functional through the
existing all-functional zeta-value sets; the constructors do not select a
Whittaker functional.

The normalized absolute value and residue cardinality are those of `T`.
The formal variable is `X=q^(-s)`. A supplied `AdditiveHaarMeasure ν`
provides the actual rectangular product measures. Every quotient-measure
specification uses the fixed ambient `generalLinearHaar` and subgroup
`unipotentHaar` normalizations. The constructed `unipotentQuotientHaar`
is compatible with these normalizations, and compatibility determines it
uniquely. Fourier self-duality is not required for this L-factor construction.

All positive equal ranks and larger-first unequal ranks are covered,
including `GL_1` by `n=0`. Reversing the order of the two ranks is outside
this contribution.

## Implemented existence and selection

`padicPairLPolynomialExists` splits `n ≤ r` into equality and strict
inequality. At equality, the published `equalRankAnalytic` theorem and
`EqualRankAnalyticStatement.pairLPolynomialExists` give the normalized
polynomial for the actual continuation ideal. At strict inequality,
`unequalRankCommonGenerator` supplies one normalized generator before all
rectangular-block indices, and `unequalRankAnalytic` supplies all four
analytic clauses for each block. The existing
`UnequalRankCommonGeneratorStatement.pairLPolynomialExists` bridge combines
these statements and the all-functional model bridge into the full
`PairLPolynomialExists` relation. The common-generator theorem is imported
by Lean name; no block-independence premise remains.

`padicPairLPolynomialExists_canonical` specializes existence to
`unipotentQuotientHaar` using its proved compatibility. The polynomial
constructor then applies the existing `pairLPolynomial` selector to that
proof. `padicPairLPolynomial_spec` proves `IsPairLPolynomial` for every
compatible quotient measure: uniqueness identifies the measure with the
constructed one, and `pairLPolynomial_spec` supplies the characterization.
For unequal ranks this is one polynomial certified at every permitted
rectangular block, rather than separately chosen block polynomials.

`padicPairLPolynomial_coeff_zero` gives constant coefficient one.
`padicPairLPolynomial_eq` proves equality with any polynomial satisfying
the same relation at any compatible measure, by the existing uniqueness
theorem. The constant coefficient also ensures the selected polynomial is
nonzero through the existing factor construction.

`padicPairLFactor` applies the existing `pairLFactor` constructor to the
proved canonical existence result. Its output is an actual rational-function
unit. `coe_padicPairLFactor` identifies its value with the reciprocal of the
selected polynomial embedded into `RatFunc ℂ`.
`padicPairLFactor_eq` gives that reciprocal formula for any certified
polynomial, and `padicPairLFactor_eq_canonicalPairLFactor` proves agreement
with the earlier supplied-topology constructor for every existence witness.
These comparisons reuse uniqueness; they introduce no factor-existence
premise into the new constructors.

## Generic specialization

`genericPairLPolynomial` and `genericPairLFactor` use the field's canonical
topological data and the published `GenericModel` bridges from standard
`Whittaker.IsGeneric` to full standard and inverse Whittaker type.
Genericity includes irreducibility, admissibility and a nonzero functional;
proved multiplicity one and character inversion supply the full-type
hypotheses. The generic constructors require no chosen functional,
quotient measure, analytic result or supplied topological-data argument.
They retain the rank-order proof and supplied additive Haar measure.

`genericPairLPolynomial_isPadic` proves the complete existing
`IsPadicPairLPolynomial` relation. It supplies a right-invariance witness
and compatible-measure existence, then proves the polynomial specification
for every compatible measure. Thus the universal characterization is not
vacuous. `genericPairLPolynomial_eq` proves uniqueness against that full
relation, and `genericPairLFactor_eq` gives the reciprocal characterization.
The coercion and constant-coefficient lemmas also specialize directly.

## Original source and derived provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.1, printed pp.385–386, gives the full Whittaker-type conventions.
Theorem 2.7(i)–(ii), pp.390–391, gives convergence and the reciprocal
polynomial with constant term one generating the Laurent fractional ideal.
Original pp.393–395 were directly visually read for this consumer: the
unit integral finishes equal-rank normalization on p.393; equation (7)
and the fixed-denominator reduction give a generator for each unequal
block on p.394; the adjacent-block argument on pp.394–395 proves those
generators agree. The source's ranks are `r_source=r+1` and `t_source=n+1`.

This module is derived composition of published constructions and theorems,
not a new proof of those analytic arguments. Its substantive inputs are
[EqualRankAnalyticProof](EqualRankAnalyticProof.md),
[UnequalRankAnalyticProof](UnequalRankAnalyticProof.md),
[UnequalRankCommonGeneratorProof](UnequalRankCommonGeneratorProof.md),
[PairLFactor](PairLFactor.md), [CanonicalPairLFactor](CanonicalPairLFactor.md),
[GenericModel](GenericModel.md), and [PadicPairFactors](PadicPairFactors.md).
Existence at the canonical measure, transport to every compatible measure,
and the uniqueness and reciprocal lemmas are internal consequences of
those definitions and proved properties. No unpublished proof draft is
reused. The earlier [PadicEqualRankLFactor](PadicEqualRankLFactor.md)
remains a separately reusable equal-rank construction; uniqueness of the
shared polynomial relation determines the same normalized polynomial.

This contribution does not assert independence from the supplied additive
Haar measure, a reversed-rank construction, functional equations, or
epsilon/gamma and nongeneric classification-based factor constructions.
Those remain separate obligations of the broader task.
