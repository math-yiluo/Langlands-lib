# Exact K0 realization is bijective

Authors: Worker 981 and Worker 585.

This module proves the published statement
`Langlands.VirtualRepresentation.Weil.ExactRealizationBijectiveStatement.{uG,uV} G`
and its three consequences. The statement says that the canonical map
`Weil.realizeExact G`, from the integer lattice on genuine continuous
irreducible complex classes of all positive ranks to the exact quotient
`Weil.ContinuousExactGroup G`, is bijective.

The proved theorems are:

- `Weil.exactRealizationBijective G : ExactRealizationBijectiveStatement.{uG, uV} G`
- `Weil.exactExpansionUnique G : ExactExpansionUniqueStatement.{uG, uV} G`
- `LocalWeil.exactRealizationBijective F : LocalWeil.ExactRealizationBijectiveStatement.{uF, uW} F`
- `LocalWeil.exactExpansionUnique F : LocalWeil.ExactExpansionUniqueStatement.{uF, uW} F`

In the generic theorems, `G : Type uG` is arbitrary with only `[Group G]` and
`[TopologicalSpace G]`. The carrier universe `uV` is independent. In the local
theorems, `p` is any prime (`[Fact p.Prime]`) and `F : Langlands.PadicField.{uF} p`
is arbitrary. The carrier universe `uW` is independent. There are no other
hypotheses. The exact quotient is the published one: its relations come from
actual short exact sequences of continuous finite-dimensional representations,
semisimple or not. Every element of the quotient is covered, including zero and
negative virtual classes.

## Inputs

- `Weil.ExactCoefficients` (helper module of this proof group) defines the
  integer-linear map `exactCoefficients G : ContinuousExactGroup G →ₗ[ℤ]
  IrreducibleLattice G`. On a continuous representation `A` it is the sum
  `coefficients A = seriesSum A (series A) _` of the lattice generators of the
  graded factors of a chosen composition series. The module proves
  `exactCoefficients_realizeExact`, so `exactCoefficients` is a left inverse,
  and `realizeExact_injective`. Its Markdown explains how Jordan–Hölder
  multiplicities make the map well defined and exact-additive.
- `Weil.ExactFiltration` (Worker 585, published) proves
  `exactClass_eq_sum_of_filtration`: for any zero-to-full filtration `s` of an
  actual continuous `A`, the exact class of `A` is the sum of the exact classes
  of the continuous graded quotients `continuousFiltrationGraded A s i`. Its
  continuity input is Worker 585's published
  `Weil.Representation.SubquotientContinuity`.

## Surjectivity

`realizeExact_seriesSum` states that for a filtration `s` with simple factors,
`realizeExact G (seriesSum A s hs)` equals the exact class of `A`.
`realizeExact` is linear, so it maps the sum to the sum of the images of the
generators. `basisOf` of each graded factor is literally the published
`basisClass` of that factor, with its rank. So `realizeExact_ofRepresentation`
sends each generator to the exact class of the graded factor. Rewriting the
class of `A` by `exactClass_eq_sum_of_filtration` makes the two sums agree term
by term.

`realizeExact_comp_exactCoefficients` proves
`(realizeExact G).comp (exactCoefficients G) = LinearMap.id`. By
`ExactGrothendieckGroup.hom_ext` it suffices to check this on each genuine
continuous class. `ExactGrothendieckGroup.lift_ofClass` turns
`exactCoefficients` there into `coefficients A` for a representative `A`. This
is `seriesSum` of the chosen series, so `realizeExact_seriesSum` finishes the
check. `realizeExact_surjective` follows: `exactCoefficients G x` is a preimage
of each `x`.

## Closing theorems

`Weil.exactRealizationBijective` pairs `realizeExact_injective` (from
`ExactCoefficients`) with `realizeExact_surjective`. This is precisely
`Function.Bijective (realizeExact G)`, the published statement.
`Weil.exactExpansionUnique` applies the forward direction of the published
`Weil.exactRealizationBijective_iff_uniqueExpansion`.

For the local Weil group, `LocalWeil.realizeExact F` is by definition the
generic `Weil.realizeExact (localWeilGroup F)`, using the existing local
lattice and exact quotient. `LocalWeil.exactRealizationBijective` is therefore
the generic theorem at `localWeilGroup F`.
`LocalWeil.exactExpansionUnique` applies the published local equivalence
`LocalWeil.exactRealizationBijective_iff_uniqueExpansion`.

## Scope

The proof uses no semisimplicity, invariant complement, unitarity, finite image
or topological-group hypothesis, and no decomposition hypothesis. The target
statements and their imports are unchanged. Together, the two inverse
identities make `exactCoefficients G` a two-sided inverse of `realizeExact G`.
It is constructed from composition series. It is not assumed. The proof route
is the finite-dimensional Jordan–Hölder argument described in
`Weil.ExactRealizationStatement.md`. No new literature claim is made.
