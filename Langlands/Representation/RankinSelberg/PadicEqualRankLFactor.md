# Constructed equal-rank p-adic L-factors

Author: Worker 31.

This module constructs the normalized L-polynomial and L-factor of actual
representations of `GL_(n+1)(F)` over a p-adic field. It uses the proved
`equalRankAnalytic` theorem to discharge normalized-generator existence.
The resulting constructors take full Whittaker-type hypotheses, or the
existing genericity hypotheses in the canonical specialization. They take
no analytic-existence hypothesis, preferred functional or quotient measure.
The field universe `uF` and the two carrier universes `uV`, `uW` are independent.
Coefficients are complex numbers, and rank one is included by `n = 0`.

## Scope and normalization

The supplied-data API retains every `F : PadicField p` and
`T : F.TopologicalData`. Its explicit `letI` telescopes install exactly the
supplied topology, valuative relation and local-field structure, the proved
second-countability instance, and Borel structures on the field, general
linear group, upper-unipotent subgroup and left quotient. Representation
carriers are algebraic complex modules; no carrier topology is required.
The standard and inverse standard characters are the existing characters
of the actual matrix upper-unipotent subgroup. The reused
`UnitaryAdditiveCharacter` includes continuity and nontriviality.

The first representation has
`IsOfWhittakerType n (standardCharacter ψ n) π`; the second has
`IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`. Each means
admissibility, finite generation over the complex group algebra, and a
linear equivalence from the entire corresponding functional space to `ℂ`.
Irreducibility is not required for these supplied-data constructors.

The residue cardinality is `q = T.residueCardinality`, the absolute value
is `normalizedAbsoluteValue T`, and the rational-function variable is
`X = q^(-s)`. `equalRankZetaValues` is the existing set of continuations of
actual equal-rank JPSS integrals over all standard and inverse Whittaker
coefficients and Schwartz–Bruhat row tests. Its definition requires absolute
convergence on a right half-plane and rational continuation of that integral;
it is not an arbitrary set of assigned factors.

## Constructed polynomial and unit

`padicEqualRankNormalizedGeneratorExists` applies the closed theorem
`equalRankAnalytic F T n` through
`EqualRankAnalyticStatement.normalizedGeneratorExists`. That bridge extracts
nonzero functionals from full type and identifies each chosen coefficient
model's rational values with the all-functional zeta-value set. Thus it
proves existence for every compatible quotient measure without leaving
any expansion, convergence, common-denominator or unit-value premise.

`padicEqualRankNormalizedGeneratorExists_canonical` specializes to the
constructed `unipotentQuotientHaar`, using its proved compatibility theorem.
Ambient general-linear and subgroup Haar measures retain the existing
compact-open normalizations. Unipotent right invariance is supplied by the
imported unimodularity construction. No quotient-measure existence or
compatibility assumption remains on the constructors.

`padicEqualRankLPolynomial` selects the polynomial using the existing
`normalizedPolynomial` and this proved existence. Its specification is
`IsEqualRankLPolynomial` at every compatible quotient measure. The proof
first uses `unipotentQuotientHaar_unique` to identify that measure with the
constructed one, then applies `normalizedPolynomial_spec`. In particular,
its constant coefficient is one, and its reciprocal generates the Laurent
span of the actual zeta values. `padicEqualRankLPolynomial_eq` uses the
proved uniqueness of normalized generators to identify it with every
certified polynomial for any compatible measure.

`padicEqualRankLFactor` applies the existing `equalRankLFactor` to the
proved canonical existence. Its value is a unit of `RationalFunctions`,
whose coercion is exactly the inverse of the polynomial's image under
`algebraMap ℂ[X] RationalFunctions`. The existing unit construction uses
the polynomial's constant coefficient to prove nonvanishing.
`padicEqualRankLFactor_eq` gives the same reciprocal formula for any
certified polynomial at any compatible measure.

`padicEqualRankLPolynomial_isPair` reduces the existing unified
`IsPairLPolynomial` relation by `isPairLPolynomial_self`.
`padicEqualRankLFactor_eq_canonicalPairLFactor` then compares coercions by
the reciprocal specifications and applies `Units.ext`. It proves equality
with the existing canonical pair constructor for every proof of that
constructor's existence premise and every additive Haar measure `ν`.
That additive measure is absent from the equal-rank integral and from the
new polynomial and unit constructors.

## Generic representations

`genericEqualRankLPolynomial` and `genericEqualRankLFactor` specialize to
`F.canonicalTopologicalData`. Their hypotheses are exactly
`Whittaker.IsGeneric ψ n π` and `Whittaker.IsGeneric ψ n σ`: irreducibility,
admissibility and a nonzero standard Whittaker functional. The proved
bridges in [GenericModel](GenericModel.md) supply full standard and inverse
Whittaker type using multiplicity one and character inversion. No scalar
multiplicity assumption or supplied nonzero functional remains.
The local `canonicalNormedField` topology is definitionally the topology
of `canonicalTopologicalData`.

`genericEqualRankLPolynomial_isPadic` proves the existing
`IsPadicPairLPolynomial` relation, including its compatible-measure existence
clause and its universal quantifier over compatible measures. The first
clause uses the proved unipotent unimodularity and compatible measure
construction; the second uses `padicEqualRankLPolynomial_isPair`.
`genericEqualRankLPolynomial_eq` invokes uniqueness of that relation.
`coe_genericEqualRankLFactor` and `genericEqualRankLFactor_eq` give the
reciprocal characterization, both for the selected polynomial and for any
certified p-adic pair polynomial.

## Provenance

This is a derived construction from the published
[equal-rank analytic theorem](EqualRankAnalyticProof.md),
[model-value bridge](AnalyticBridge.md),
[Laurent normalization](RationalZeta.md),
[actual quotient measure](UnipotentQuotient.md),
[normalized-factor constructors](LocalFactor.md),
[canonical pair constructor](CanonicalPairLFactor.md), and
[p-adic pair relation](PadicPairFactors.md). It composes their proved
existence, uniqueness and compatibility results; none is a new premise or
axiom here. The new contribution is the actual selection of the equal-rank
polynomial and unit with these prerequisites discharged, including its
generic specialization and agreement with the existing relations.

The original normalization is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), Theorem 2.7(i)–(ii), printed pp.390–393. The theorem states
convergence, rationality, the fractional ideal, and the reciprocal-polynomial
normalization `L(s, π × σ) = P(q^(-s))⁻¹`, `P(0) = 1`; its proof on p.393
uses an actual integral equal to one to obtain the normalized generator.
The original scan's retained PDF pp.25–28 were read visually for this
construction. The Whittaker-type and generic-model conventions come from
Section 2.1, printed pp.385–386, read for GenericModel. Registered source:
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No source-specific errata note was present in the checked project and
Library locations. The analytic proof and its source correspondence remain
in the imported theorem's paired Markdown.

This focused construction covers equal positive ranks. Unequal-rank
analytic existence, functional equations, epsilon and gamma existence,
and nongeneric Langlands-classification constructions retain their separate
owners and proof obligations.
