# The horizontal differential on an actual automorphic realization

This internal construction restricts the existing actual coefficient Lie
differential to the horizontal full-compact-equivariant reduced cochains
with coefficients in `S.Space`, for an actual `OperatorRealization F n`
over a number field `F : Type u`. All scalars are complex. The reduced
Lie action is constructed for every natural rank; the horizontal
differential requires positive rank, as does the reduced compact
differentiation theorem it uses. No new representation carrier or
compatibility hypothesis is supplied.

`reducedLieAction` is the restriction of `S.complexLieAction` along
`reducedComplexInclusion`. Its Lie module instances pull back the actual
complex Lie module along the same inclusion. The application and bracket
lemmas identify the resulting operators. `reducedLieAction_compact`
proves that restricting again through the actual compact-to-reduced
inclusion agrees with `S.compactLieAction`. The finite adelic action
commutes with the reduced action by the existing complex-action theorem.
Full compact covariance follows from the proved complex-action covariance
and equivariance of the reduced inclusion under actual conjugation.

The reduced Lie restrictions of a full intertwiner or equivalence retain
the existing underlying linear map or linear equivalence. Their Lie
equations specialize the full differential intertwining equation.

For a horizontal full-compact-equivariant cochain, every direction in
`compactInReducedSubmodule` has a preimage under `compactToReducedComplex`.
`horizontalCochain_infinitesimal` takes that preimage, identifies its
reduced coefficient action with the actual compact Lie action, and
applies `S.reducedCochain_compact_complex` to the full compact equivariance
of the cochain. Thus the required infinitesimal insertion identity is a
proved consequence, including in degree zero.

`horizontalDifferential` instantiates the generic
`Langlands.Cohomology.Lie.horizontalEquivariantDifferential` using the
actual reduced adjoint action, the actual compact coefficient action,
the proved covariance and the preceding insertion identity. Its value
is exactly the existing coefficient differential, as the value and
application lemmas record. The codomain retains both every-slot
horizontality and equivariance under the entire standard compact group,
including its disconnected components.

The provenance is internal composition and restriction of
`OperatorLieAction`, `OperatorCompactCompatibility`,
`ArchimedeanRelativeAdjoint`, `ArchimedeanHorizontal`,
`ReducedCochainCompactDifferentiation` and the generic
`Cohomology.Lie.HorizontalDifferential`. No external identification of
cohomology is asserted. This module does not establish square zero,
construct cycles, boundaries or cohomology, attach general algebraic
tensor coefficients, or assert the cohomological infinity condition.

Authorship: Worker 2.
