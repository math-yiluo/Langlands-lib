# Actual horizontal cohomology of an automorphic realization

This internal construction specializes
`Langlands.Cohomology.Lie.Horizontal.HorizontalCohomology` to the actual
horizontal differential on an `OperatorRealization F n`. The number field
`F : Type u` has arbitrary universe and the natural rank `n` is positive, as
required by the actual horizontal differential. Coefficients belong to the
existing complex module `S.Space`. Every natural cochain degree, including
zero, is covered.

## Actual actions and proved compatibility

The specialization uses exactly `compactInReducedSubmodule F n`,
`reducedCompactRepresentation F n` and `S.compactRepresentation`. Bracket
covariance is supplied by the actual reduced conjugation Lie equivalence,
and coefficient covariance by
`S.compactRepresentation_reducedLieAction`. The all-degree infinitesimal
insertion identity is the published `S.horizontalCochain_infinitesimal`,
proved using actual compact differentiation. No compatibility hypothesis is
added to the input `S`.

The cochain module in degree `q` is definitionally
`horizontalEquivariantSubmodule F n S.compactRepresentation q`. Its elements
are alternating maps from the actual reduced complex Lie algebra into
`S.Space`, vanish whenever any argument belongs to the actual compact Lie
image, and are equivariant for every element of the full standard infinite
compact group. Its disconnected components remain present. The specialized
generic differential is definitionally the published
`S.horizontalDifferential q`, with the actual reduced coefficient Lie action.
Neither a cochain carrier nor a differential is supplied as a new input.

## Actual submodules and quotient

`horizontalCycles q` abbreviates the specialized generic kernel of this same
differential. `horizontalBoundaries 0` is the bottom submodule, and
`horizontalBoundaries (q + 1)` is the actual range of
`S.horizontalDifferential q`.

`horizontalBoundariesInCycles q` abbreviates the specialized generic range
of the proved boundary inclusion into `S.horizontalCycles q`. The inclusion
is already proved in the generic construction: its square-zero theorem uses
subtype extensionality and the published coefficient theorem
`Langlands.Cohomology.Lie.differential_differential`; bottom supplies the
inclusion in degree zero and square zero supplies it in successor degrees.
No square-zero or boundary-inclusion hypothesis is required from `S`.

`HorizontalCohomology q` abbreviates the specialized Mathlib complex module
quotient of cycles by this inclusion range. `horizontalCohomologyClass q`
is its linear quotient projection, specialized from the generic
`cohomologyClass`. The actual actions and all compatibility proofs are fixed
by `S`, the number field and the rank.

## Provenance and scope

This is an internal specialization of the constructed generic horizontal
cohomology to the published actual automorphic horizontal differential and
its proved action compatibilities. The generic construction uses the actual
coefficient differential, kernels, actual ranges, the proved inclusion and
Mathlib module quotients. No new external-literature identification is
asserted.

This focused module supplies the actual cycles, boundaries, quotient and
projection. Explicit automorphic-namespaced class lemmas, finite adelic
quotient action and transport by full operator maps are separate units.
No sheaf, analytic or Ext comparison, general algebraic tensor coefficient
attachment, cohomological infinity criterion or nonvanishing theorem is
asserted.

Authorship: Worker 2.
