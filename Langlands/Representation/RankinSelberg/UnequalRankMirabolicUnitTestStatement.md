# Compact mirabolic unit tests for every unequal-rank JPSS block

Author: Worker 481. Worker 356 supplied the focused target specification.

The module defines the proposition
`Langlands.RankinSelberg.UnequalRankMirabolicUnitTestStatement.{uF,uW} F T n j k`.
It states an internal compact test construction used before the Kirillov
lift in the unequal-rank unit-span argument. This file states the construction
target; it supplies neither witnesses nor a proof.

## Data and hypotheses

The statement is uniform in every prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, and all
`n j k : ℕ`. The smaller rank is `t = n + 1`, the larger rank is
`r = n + (j + k + 1) + 1`, and their difference is `j + k + 1`.
Thus every positive rank gap and every allowed block are covered. The
cases `n = 0`, `j = 0`, `k = 0`, and `j = k = 0` are included.

The local instances are exactly those installed by
`UnequalRankUnitSpanStatement`: `T.topology`, `T.valuativeRel`, `T.localField`,
the Borel measurable structure on the field, and Borel structures and
`BorelSpace` certificates on the smaller general linear group, its actual
upper-unipotent subgroup and their left quotient. No canonical replacement
for the supplied topology is chosen.

For every `ψ : UnitaryAdditiveCharacter F.Carrier`, the statement retains
the right-invariance instance for the actual `unipotentHaar F.Carrier n`.
It quantifies every quotient measure `μ` satisfying `IsCompatible` with
the actual `generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`,
and every `ν : AdditiveHaarMeasure F.Carrier`. In particular, no scalar
normalization of `ν` is imposed.

The carrier `W : Type uW` has an additive commutative group and complex
module structure, with no topology on `W`. For every representation `σ`
of `GL_(n+1)(F)` on `W`, the representation hypothesis is precisely
`IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`. This is the
published conjunction of admissibility, finite generation over the group
algebra, and a one-dimensional space of functionals for that character.
For every actual `ℓ' : glInverseFunctionals ψ n σ` with `ℓ'.val ≠ 0`,
the conclusion concerns the coefficient model of this specified functional.
The universes `uF` and `uW` are independent.

## Exact witnesses and integral

The conclusion supplies one pair

```lean
φ : WhittakerFunctions ψ (n + (j + k + 1))
f' : (coefficientModel σ ℓ').toSubmodule
```

such that `IsMirabolicTestFunction ψ (n + (j + k + 1)) φ`, and for
every `s : ℂ` simultaneously,

```lean
UnequalRankConverges ψ (normalizedAbsoluteValue T) j k
  μ (rectangularMeasure ν j (n + 1)) φ f'.val s
```

and

```lean
unequalRankIntegral ψ (normalizedAbsoluteValue T) j k
  μ (rectangularMeasure ν j (n + 1)) φ f'.val s = 1
```

hold. The witnesses may depend on all preceding data, including both
measures, but are chosen before `s`. The smaller function is an actual
coefficient `g ↦ ℓ'(σ(g)w)`, rather than an arbitrary inverse-equivariant
function.

The imported `Langlands.Whittaker.IsMirabolicTestFunction` from
`Whittaker.ModelKirillovStatement` adds right smoothness and compact support
modulo upper unipotents on the mirabolic restriction of the existing
globally equivariant function `φ`. It uses the actual last-row mirabolic
condition. This module introduces no replacement predicate or group.
Values off that subgroup remain subject only to the existing global
covariance; no smoothness or support condition is added there.

The integral and convergence predicate are the existing actual ones in
`RankinSelberg.QuotientIntegrals`. On a representative `g` of the smaller
left-unipotent quotient, the integrand is the product of the value of `φ`
at `unequalRankMatrix j k g x`, the smaller coefficient at `g`, and
`determinantWeight (normalizedAbsoluteValue T) g
  (s - ((j + k + 1 : ℕ) : ℂ) / 2)`.
Representative independence is supplied by the existing quotient integrand.
`UnequalRankConverges` means integrability of that complex function on the
product measure
`μ.prod (rectangularMeasure ν j (n + 1))`.
The literal integral is the nested Bochner integral with the rectangular
variable integrated first and the quotient variable second.

The rectangular measure is exactly the nested finite product of `ν.measure`,
with `j` rows and `n + 1` columns. At `j = 0`, the published
`rectangularMeasure_zero_rows` identifies it with unit point mass on the
unique zero-row matrix. All-parameter product integrability is an explicit
conclusion, so the totalized integral alone cannot discharge it.

No larger representation, larger functional, Kirillov proposition,
pre-existing test function, rationality, common denominator, Iwasawa theorem
or fixed Haar normalization is an antecedent. Later lifting and comparison
arguments can use these witnesses to address `UnequalRankUnitSpanStatement`;
this definition does not prove that statement either.

## Original source and internal separation

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.385–386 and 393–394 were read visually from one-based PDF
pages20–21 and 28–29. No JPSS-specific errata filename was found in the
checked Library notes, project notes or literature locations.

Section 2.1 on printed pp.385–386 defines representations of Whittaker type
and their coefficient functions. Section 2.2 on p.386 defines the smooth
covariant functions on the mirabolic subgroup with support compact modulo
the upper-unipotent subgroup, and states their inclusion in restrictions
of the Whittaker model, citing [G-K]. This module relies on that JPSS
passage, without claiming an independent reading or proof of [G-K].

The unit-value argument on p.393 first chooses compact mirabolic data and
their coefficient-model lifts in the equal-rank case, and then begins
the unequal-rank argument with compactness of the rectangular variable.
On p.394 the source explicitly asserts that each unequal-rank fractional
ideal contains one, again invoking the mirabolic restriction inclusion.
This motivates the present existence statement.

The separation of raw compact test construction from the subsequent
Kirillov lift is internal to this formalization. JPSS asserts the
resulting unit step; these pages do not supply the construction required by
this exact interface. The arbitrary supplied topology, explicit product
measure, integrability for every complex parameter and literal integral-one
witnesses specify the implementation obligations. A proof must establish
the block-support description, finite positive volumes and the rescaling
for arbitrary `μ` and `ν`, including the empty rectangular factor at `j = 0`.
Merely defining this proposition establishes none of these facts.

## Lean validation

Development `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the entry module with zero
errors and warnings. Exact declaration inspection reported
`statement_returns_prop: true`, independent universe parameters `uF` and
`uW`, and only `propext`, `Classical.choice` and `Quot.sound` among its
axioms. This verifies the proposition definition, not its truth.
