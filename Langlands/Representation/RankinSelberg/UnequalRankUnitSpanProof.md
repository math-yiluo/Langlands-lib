# Unit membership in every actual unequal-rank JPSS zeta span: proof

Author: Worker 356.

`Langlands.RankinSelberg.unequalRankUnitSpan` proves the published proposition
`Langlands.RankinSelberg.UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k`.
Its complete type is

```lean
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ),
  Langlands.RankinSelberg.UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k
```

The field and two representation universes remain independent. The proof
retains the supplied topological data `T`, all natural `n`, `j`, `k`,
every compatible quotient measure `μ`, every additive Haar measure `ν`,
both representations of Whittaker type and both specified nonzero functionals.
It covers smaller rank one (`n = 0`), the zero-row block (`j = 0`) and
corank one (`j = k = 0`) without a separate argument.

## Published inputs

The proof imports three proved interfaces by Lean name.

- `RankinSelberg.unequalRankMirabolicUnitTest` supplies a larger raw test
  `φ`, an actual smaller coefficient `f' ∈ coefficientModel σ ℓ'`,
  `IsMirabolicTestFunction φ`, and convergence and integral one for every
  complex parameter. This is uniform in the supplied `T`, `μ` and `ν`.
- `Langlands.whittakerTypeKirillov` proves canonical Kirillov lifting,
  retaining the full Whittaker-type scope.
- `Whittaker.modelKirillovTransfer` transports that theorem to the supplied
  topology and the actual coefficient image of the specified nonzero large
  functional `ℓ`. It produces `f ∈ coefficientModel π ℓ` agreeing with
  `φ` at every matrix whose last row is the last coordinate row.

These inputs were proved respectively by Workers 856, 127 and 654. They are
imported theorems; this module adds the block and integral comparisons and
the final span argument.

The arbitrary Haar normalization is handled by the first input, not by
changing the measures in this module. Its construction uses a common
positive principal congruence level and has exact support `Ω × X`, where
`Ω` is a compact open quotient orbit and `X` consists of matrices with
entries in that level ideal. Both supplied measures give these sets finite
positive mass. It scales the smaller coefficient by
`(μ.real Ω * (rectangularMeasure ν j (n + 1)).real X)⁻¹` and the inverse
of its nonzero value at the identity. Thus the nested integral equals one
for the supplied measures. When `j = 0`, the rectangular mass is one.
The details are in the imported proof's paired Markdown.

## Implemented deduction

All helper lemmas are in `Langlands.RankinSelberg.UnitSpanAssembly`.

`block_last_row` expands `unequalRankMatrix_val` and
`appendIdentity_entry`. In the matrix

```text
[ g  0  0 ]
[ x  I  0 ]
[ 0  0  I ]
```

the last row is outside both the leading block and the rectangular block:
their row ranges end before it, since `j + k + 1` is positive.
The last row is consequently the last coordinate row. This calculation
uses only field algebra and natural-number inequalities.

`integrand_eq_of_mirabolic_eq` applies this fact on every quotient
representative. Two larger Whittaker functions agreeing on mirabolic
matrices give identical actual unequal-rank integrands for the same smaller
function. Their product with the smaller coefficient and the determinant
weight is unchanged. `converges_iff_of_mirabolic_eq` rewrites the resulting
product-measure integrability predicate.
`integral_eq_of_mirabolic_eq` rewrites the actual nested Bochner integrals.
The integral comparison itself needs no integrability assumption.
These lemmas allow arbitrary displayed measures; the final application
uses exactly `μ` and `rectangularMeasure ν j (n + 1)`.

`one_mem_of_unit_integral` starts with actual coefficient-model vectors
whose integral is one for every `s : ℂ`. In the definition of
`unequalRankRationalValues`, these vectors witness the constant rational
function one: choose right half-plane bound zero, use `RatFunc.denom_one`
to obtain denominator nonvanishing, and use `RatFunc.eval_one` for its
evaluation at `T.residueCardinality ^ (-s)`. Thus one is one of the actual
rational values. `Submodule.subset_span` puts it in the requested
`Submodule.span LaurentCoefficients`, namely `zetaSpan`.
The conclusion of the final theorem is precisely the published span
membership.

`one_mem_of_mirabolic_unit_integral` combines that argument with the nested
integral comparison. `unitSpan_of_kirillov_and_compact_test` installs the
same supplied topology, valuative relation, local-field and Borel instances
as the statement. It obtains `φ` and `f'` from the compact-test interface,
and applies `Whittaker.modelKirillovTransfer` to get the actual large
coefficient `f`. Mirabolic agreement then transfers integral one and proves
the span membership for these actual models. The compact-test input also
provides convergence; only its integral-one component is needed to satisfy
this target.

`unitSpan_of_compact_test` supplies the published canonical Kirillov
theorem to this assembly. The final `unequalRankUnitSpan` supplies the
published compact-test theorem, so its complete type has no additional
premise. Both intermediate premises have been discharged. The proof uses
no irreducibility or unitary-central-character assumption.

## Original source and provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, is registered as `jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 356 read printed pp.385–386 and 393–394 visually, at zero-based PDF
indices 19–20 and 27–28. No source-specific registered errata were found
in the checked project and Library notes.

Section 2.1, pp.385–386, gives Whittaker-type representations and their
actual coefficient functions. Section 2.2, p.386, gives the smooth covariant
compact-modulo-unipotent functions on the mirabolic subgroup and their
inclusion in the restricted Whittaker model. On p.393 the test-vector
argument uses such functions to obtain integral one and starts the
unequal-rank compact-support argument. On p.394 JPSS asserts that the
Laurent ideal `I_j` contains one, using the same mirabolic inclusion.
This is the source of the proposition proved here.

The helper comparisons and the passage through the Library's exact
rational-continuation and span definitions are internal deductions. The
principal-level construction and inverse-mass scaling belong to the
imported compact-test proof; they make the source's test-vector route
explicit for all supplied measures. The imported canonical Kirillov proof
uses compact mirabolic minimality; its own Markdown records its
Bernstein–Zelevinsky source and implemented route. This module uses that
proved inclusion and adds no new source claim about its proof.

The result proves unit membership for every block. General rationality
and convergence for every coefficient pair, common denominators,
normalized generators and independence of the block remain separate
results.

## Development validation

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the entry module with zero errors and warnings. Inspection of the
final theorem reported universe parameters `uF`, `uV`, `uW` in that order
and only `propext`, `Classical.choice` and `Quot.sound` among its axioms.
This development check is separate from independent review, exact-target
validation and publication.
