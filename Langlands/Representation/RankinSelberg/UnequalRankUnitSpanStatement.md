# Unit membership in every actual unequal-rank JPSS zeta span

Author: Worker 356. Worker 329 supplied the focused target specification.
The module defines the proposition
`Langlands.RankinSelberg.UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k`.
It states the unit-membership step in the unequal-rank proof of JPSS
Theorem 2.7. It does not prove that proposition.

## Data and hypotheses

The module imports the published `RankinSelberg.AnalyticStatement`. It copies
the field, topology, rank parameters, local instances and quantified hypotheses
of `UnequalRankAnalyticStatement` exactly, replacing only the final conclusion.
The definition is uniform in every prime `p`, `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, and natural numbers `n`, `j`, `k`.
It installs `T.topology`, `T.valuativeRel` and `T.localField`, the Borel
structure on `F.Carrier`, and the Borel structures and certificates on
`GL_(n+1)`, its upper-unipotent subgroup and their left quotient.
It makes no restriction to canonical topological data.

The quantified character `ψ : UnitaryAdditiveCharacter F.Carrier` is already
continuous, nontrivial and unitary by its definition. The statement retains
the explicit right-invariance instance for `unipotentHaar F.Carrier n`.
It quantifies every quotient measure `μ` satisfying `IsCompatible` with
the actual normalized `generalLinearHaar` and `unipotentHaar`, and every
additive Haar measure `ν` on the field.

The independent carriers `V : Type uV` and `W : Type uW` have their own
additive-group and complex-module structures. The larger representation `π`
has rank `r = n + (j + k + 1) + 1`; the smaller representation `σ` has
rank `t = n + 1`. Both satisfy the published `IsOfWhittakerType` predicate:
admissibility (including smoothness), finite generation over the group
algebra, and a one-dimensional space of functionals for the specified
character. That character is the standard character for `π` and the inverse
standard character for `σ`. The statement quantifies every corresponding
pair of functionals `ℓ`, `ℓ'` with `ℓ.val ≠ 0` and `ℓ'.val ≠ 0`.

Thus `n = 0` includes smaller rank one, and `j = 0` and `k = 0` are allowed.
The gap `r - t = j + k + 1` covers every positive gap and every block
`0 ≤ j ≤ r - t - 1`. In particular, `j = k = 0` is the corank-one case.
There are no irreducibility or unitary-central-character assumptions.
Convergence, rationality, a common denominator, a normalized generator and
a Kirillov restriction conclusion are not hypotheses.

## Exact conclusion

The conclusion is

```lean
(1 : RationalFunctions) ∈ zetaSpan
  (unequalRankRationalValues j k T.residueCardinality ψ
    (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')
```

The existing `RationalFunctions` is `RatFunc ℂ`, and `zetaSpan values` is
`Submodule.span LaurentCoefficients values`, where `LaurentCoefficients`
is the Laurent polynomial ring over `ℂ`. Its scalar action on rational
functions comes from the published embedding sending the Laurent variable
to the rational-function variable `X`. Unit membership means that a finite
Laurent linear combination of the actual rational values is `1`. The
statement neither replaces this with mere nonvanishing nor strengthens it
to membership of `1` in the raw value set.

The existing `unequalRankRationalValues` consists of rational functions `R`
for which there are actual vectors in `coefficientModel π ℓ` and
`coefficientModel σ ℓ'` whose `unequalRankModelIntegral` has rational
continuation `R`. The coefficient-model functions have the form
`g ↦ ℓ(π(g)v)` and `g ↦ ℓ'(σ(g)w)`. `HasRationalContinuation` requires
agreement with `R(q^(-s))` throughout a right half-plane, with the denominator
nonzero there. Here `q = T.residueCardinality` and the absolute value is
the existing `normalizedAbsoluteValue T`.

The inner matrix measure is exactly

```lean
Measure.pi (fun _ : Fin j =>
  Measure.pi (fun _ : Fin (n + 1) => ν.measure))
```

as defined by `rectangularMeasure`. No independent matrix measure is
substituted. At `j = 0` the existing zero-row theorem identifies it with
unit point mass. The outer measure is the quantified compatible `μ`.

The value set is meaningful before rationality for every coefficient has
been proved: it records just those rational functions witnessed by the
continuation relation. This proposition asserts that these values span `1`.
It does not assert absolute convergence for all coefficient integrals or
the existence of a rational continuation for every coefficient pair.
Those are separate clauses of `UnequalRankAnalyticConclusion`. A common
denominator and normalized-generator existence also remain separate
obligations. The chosen span-membership conclusion is the input required
by the algebraic normalization step.

## Original source and remaining proof work

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385–386 and 393–394 were read visually from this scan.
Their zero-based PDF indices are 19–20 and 27–28.

Section 2.1, printed pages 385–386, defines representations of Whittaker
type and their coefficient models. Section 2.2, printed page 386, defines
the smooth equivariant functions on the mirabolic subgroup with support
compact modulo the unipotent subgroup, and states their inclusion in the
restrictions of the Whittaker model. This is the lifting input used in the
test-vector argument; it is not an assumption in the present proposition.

The proof on printed page 393 first uses such mirabolic functions and their
lifts to obtain the equal-rank unit integral. It then begins the
unequal-rank argument using compact support in the rectangular variable.
On printed page 394, after establishing rationality and a fixed denominator,
the source forms the Laurent fractional ideal `I_j` and explicitly asserts
`I_j ∋ 1`, again invoking the mirabolic restriction inclusion. That
unequal-rank assertion is the exact source of this focused target. The
subsequent reciprocal-polynomial normalization and independence of `j`
are outside this target.

The use of the Library's supplied topology, actual coefficient models,
normalized quotient measures and nested product matrix measure is the
formal specialization inherited from `AnalyticStatement`, not extra
terminology or a new theorem attributed to JPSS. A full formal proof must
connect the mirabolic test functions and their lifts to these models,
transport the needed results to every supplied `T`, and prove the measure
and integral comparisons. It must handle arbitrary additive-Haar scaling
of `ν`, rather than assume a self-dual normalization. Merely defining this
proposition supplies none of these adapters or the test-vector proof.

## Lean validation

Development `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the entry module with no
errors or warnings. Exact declaration inspection reported a proposition-valued
definition with independent universe parameters `uF`, `uV`, `uW` and only
`propext`, `Classical.choice` and `Quot.sound` among its axioms. This checks
the statement definition; it does not prove the proposition.
