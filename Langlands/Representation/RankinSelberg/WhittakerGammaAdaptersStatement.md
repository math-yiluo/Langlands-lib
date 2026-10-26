# Whittaker character transport and uniform epsilon adapters

Worker 640 states the closed proposition
`Langlands.RankinSelberg.WhittakerGammaAdaptersStatement.{uF,uV,uW}`.
It is the conjunction of three closed, universally quantified proposition
definitions described below. This pair supplies their statements; it supplies
no proof of them and no analytic existence result. The field universe `uF` and
the two representation-carrier universes `uV` and `uW` are independent.

## Same-representation character transport

`WhittakerTypeCharacterTransportStatement.{uF,uV}` quantifies over every
field `F : Type uF`, every supplied topology with `IsTopologicalRing F`,
every `ψ : UnitaryAdditiveCharacter F`, every `n : ℕ`, every complex vector
space `V : Type uV`, and every actual representation `π` of `GL_(n+1)(F)` on
`V`. It asserts

```text
IsOfWhittakerType n (standardCharacter ψ n) π ↔
IsOfWhittakerType n (inverseStandardCharacter ψ n) π.
```

Both sides use the same representation and the same carrier. The existing
`IsOfWhittakerType` is the conjunction of admissibility, finite generation of
`π.asModule` over the group algebra, and a linear equivalence between the
specified Whittaker functional space and `ℂ`. Thus this is the full type
equivalence, not merely an equivalence of nonzero-functional existence.
No irreducibility, finite-dimensional carrier, valuation or local-field
hypothesis is added to this component. The character structure already
includes continuity, unitarity and nontriviality. Successor rank includes
rank one.

## One specified functional pair determines the same epsilon monomial

`EqualRankEpsilonUniformityStatement.{uF,uV,uW}` quantifies over every
field `F` with `ValuativeRel F`, a supplied topology, and
`IsNonarchimedeanLocalField F`. This is the existing valued local-field
topology. It takes supplied measurable and Borel structures on `F`,
`GL_(n+1)(F)`, its upper unipotent subgroup, and its left unipotent quotient.
It quantifies independently over complex vector spaces `V : Type uV` and
`W : Type uW`, over `q : ℕ`, `ψ : UnitaryAdditiveCharacter F`,
`abv : AbsoluteValue F ℝ`, a supplied scalar additive Haar measure
`ν : AdditiveHaarMeasure F`, and representations `π` and `σ` of
`GL_(n+1)(F)` on those carriers.

Its premises are full standard Whittaker type of `π`, full inverse-standard
Whittaker type of `σ`, a specified standard functional `ℓ` and inverse
functional `ℓ'` whose underlying linear maps are nonzero, and, for the
specified `c : ℂˣ` and `m : ℤ`,

```text
EqualRankEpsilonEquation q ψ abv (unipotentQuotientHaar F n) ν
  π σ ℓ ℓ' c m.
```

Its conclusion is the existing
`IsEqualRankEpsilonFactor q ψ abv ν π σ (c, m)`, with exactly the same
coefficient and exponent. This relation includes compatible quotient-measure
existence, nonzero-functional existence, and the fixed-monomial equation
for every compatible quotient measure and every pair of nonzero
functionals. The premise assumes the equation only for the specified pair
at the constructed quotient measure; it does not assume that uniform
conclusion. The supplied `q` and `abv` are unchanged; there is no `q > 1`
premise or extra normalization hypothesis, and `ν` is not required to be
self-dual. The adapter transports a supplied equation rather than asserting
its analytic existence or uniqueness.

`UnequalRankEpsilonUniformityStatement.{uF,uV,uW}` has the same data,
with `n r : ℕ`, `hnr : n < r`, `π` of rank `r+1`, and `σ` of rank `n+1`.
Only the smaller general linear group, its unipotent subgroup and its
quotient need the supplied Borel structures. Its equation premise is the
existing `UnequalRankEpsilonEquation hnr` at
`unipotentQuotientHaar F n` for the specified nonzero functional pair and
specified `(c,m)`. Its conclusion is the unchanged
`IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ (c,m)`.
The equation premise retains its quantification over every `j k : ℕ` and
`hr : r = n + (j + k + 1)`, its rectangular product measures
`rectangularMeasure ν j (n+1)`, the complementary dual block, and its common
polynomials and central sign. No replacement epsilon equation or factor
relation is introduced.

## Sources and internal provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Printed pages 385–386 (§2.1; PDF pages 20–21) and 390–391
(Theorem 2.7; PDF pages 25–26) were read visually. No separate source
erratum note was found in the checked current Library/project
`notes/errata` locations.

Section 2.1 defines admissible finite-type Whittaker type by a
one-dimensional functional space, explains replacement of the character by
its inverse through diagonal conjugation on the same representation, and
defines the coefficient model. The first component packages that argument
in the Library's interface, with the broader topological-field scope of its
published algebraic functional-space equivalences. Theorem 2.7 supplies the
source provenance of the existing equal- and unequal-rank functional equations;
its unequal-rank epsilon factor is independent of the rectangular block.
The two fixed-certificate uniformity adapters are internal derived packaging,
not separately quoted theorems of JPSS. They do not prove Theorem 2.7 or
assert that a fixed certificate exists.

The intended derivation uses only published interfaces:

1. `Langlands.Whittaker.characterChangeFunctionalEquiv` and
   `characterChangeInverseFunctionalEquiv` at the unit `-1`, with
   `standardCharacter_scale_neg_one` and
   `inverseStandardCharacter_scale_neg_one`, transport the one-dimensional
   functional-space conjunct. Admissibility and group-algebra finite
   generation concern the same `π` on both sides.
2. `IsOfWhittakerType.eq_smul` in `RankinSelberg.AnalyticBridge` expresses
   each functional as a scalar multiple of a chosen nonzero functional.
   `whittakerSet_eq_coefficientModel` and
   `inverseWhittakerSet_eq_coefficientModel` in `RankinSelberg.LocalFactor`
   then identify the intrinsic model set with each nonzero functional's
   coefficient model. Consequently any two such coefficient models agree.
3. `EqualRankEpsilonEquation.congr_model` and
   `UnequalRankEpsilonEquation.congr_model` transport the fixed equation
   between these equal coefficient models without changing `c` or `m`.
4. `unipotentQuotientHaar_isCompatible`,
   `unipotent_compatibleMeasureExists`, and
   `unipotentHaar_isMulRightInvariant` supply the measure-existence and
   right-invariance fields already required by the factor relations.
   `unipotentQuotientHaar_unique` identifies every compatible quotient
   measure with the specified constructed measure exactly, for the same
   ambient and subgroup Haar normalizations.

These observations explain provenance and remaining proof obligations;
this module contains only proposition definitions. The distinct successor
proof task will target this exact conjunction after Library publication.
It does not duplicate the parent gamma-construction proof or any analytic
or functional-equation proof task.

Workers 31, 43, 103 and 216 supplied reused navigation and the assembly
route. Worker 471 supplied the supporting-task design for the parent
Whittaker gamma construction. They are credited with Worker 640 in the
statement submission.
