# Jordan–Hölder coefficients on the exact quotient

Author: Worker 981.

This helper module defines an integer-linear left inverse of the canonical
exact realization `Weil.realizeExact G` and concludes that the realization is
injective. The assumptions are only `Group G` and `TopologicalSpace G`; the
group universe `uG` and the representation-carrier universe `uV` are
independent. No semisimplicity, invariant complement, unitarity or
topological-group hypothesis is used.

## Construction

All results live in namespace `Langlands.VirtualRepresentation.Weil`; helpers
are in the sub-namespace `ExactCoefficients`.

- `exists_series A` gives, for every continuous finite-dimensional complex
  representation `A`, an actual composition series
  `s : ObjectRepFiltration A.val.obj n` with simple graded factors
  (`s.HasSimpleFactors`). The `ℂ[G]`-module of `A` is Noetherian and Artinian
  because it is finite-dimensional over `ℂ`. Mathlib's
  `isFiniteLength_iff_exists_compositionSeries` gives a composition series of
  submodules. The Library lemma
  `LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
  converts it into an object filtration with simple factors.
- `rank_pos_of_isIrreducible` shows that an irreducible object has positive
  rank, since a simple module is nontrivial.
- `basisOf B h` is the basis element of the published irreducible lattice
  given by an actual continuous irreducible object `B`: its class together
  with its rank as a positive natural number.
- `representative b` is a chosen actual representative (`Quotient.out`) of
  the class in a basis element `b`. `basis_ext` says a basis element is
  determined by its class, because the rank is determined by the class.
  `basisOf_eq_iff` says `basisOf B h = b` exactly when `B` is equivalent to
  `representative b`.
- `seriesSum A s hs` is the lattice element
  `∑ i, generator (basisOf (continuousFiltrationGraded A s i) (hs i))`, where
  `continuousFiltrationGraded` is the continuous graded quotient from
  `Weil.ExactFiltration`. `seriesSum_apply` shows that its coefficient at `b`
  is `s.factorMultiplicity (representative b).obj`, the number of graded
  factors equivalent to that representative.
- `coefficients A` is `seriesSum` for one chosen series (`series A`).
  `coefficients_apply` says any multiplicity witness
  `HasJordanHolderMultiplicity A.val.obj (representative b).obj m` computes
  the coefficient at `b` as `m`. This is the Library's Jordan–Hölder
  uniqueness `HasJordanHolderMultiplicity.unique`. So the coefficients do not
  depend on the chosen series.

## Descent to the exact quotient

- `coefficients_eq_of_equiv` gives equal coefficients for equivalent objects.
  It uses the Library transport `equivJordanHolderMultiplicityTransport`, so
  `classCoefficients` is well defined on genuine continuous classes.
- `classCoefficients_isExactAdditive` checks the exact relation: for an actual
  short exact sequence `A → B → C` of continuous representations, each
  coefficient of `B` is the sum of those of `A` and `C`. It applies the
  Library's `jordanHolderShortExactAdditivity` one basis element at a time,
  with the series of `A` and of `C`, and then uses `coefficients_apply` for
  `B`.
- `exactCoefficients G : ContinuousExactGroup G →ₗ[ℤ] IrreducibleLattice G`
  is `ExactGrothendieckGroup.lift` of `classCoefficients`.

## Left inverse and injectivity

`coefficients_of_isIrreducible` shows that an irreducible continuous `A` has
coefficients `generator (basisOf A h)`. The Library's
`irreducibleMultiplicity` computes the multiplicity of `representative b` in
`A`: it is `1` when they are equivalent and `0` otherwise. `basisOf_eq_iff`
matches this with the single-point function.

`exactCoefficients_comp_realizeExact` proves
`(exactCoefficients G).comp (realizeExact G) = LinearMap.id` by
`Finsupp.lhom_ext`. On a generator, `realizeExact_generator` and
`ExactGrothendieckGroup.lift_ofClass` reduce the goal to
`coefficients_of_isIrreducible`. `exactCoefficients_realizeExact` is its
pointwise form. `realizeExact_injective` follows because a function with a
left inverse is injective.

## Provenance

This is derived internal bookkeeping on the published constructions. It
follows the Jordan–Hölder rationale recorded in
`Weil.ExactRealizationStatement.md`: multiplicities do not depend on the
series and add along short exact sequences. The representation-theoretic
content (Jordan–Hölder uniqueness, additivity, the irreducible case and
invariance under equivalence) comes from the published Library results above.
This module makes no new literature claim. It proves only injectivity.
`Weil.ExactRealizationProof` uses `seriesSum` and `exactCoefficients` to prove
surjectivity and the closing statements.
