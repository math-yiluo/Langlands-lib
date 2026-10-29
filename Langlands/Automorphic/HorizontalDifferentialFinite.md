# Finite equivariance of the actual horizontal differential

Let `F` be a number field in arbitrary universe `u`, let `n` be a positive
natural rank, and let `S : OperatorRealization F n` be an actual operator
realization. The coefficients are complex and are the existing `S.Space`.
Every natural cochain degree, including zero, is included.

`horizontalDifferential_finite` proves that the actual restricted horizontal
differential commutes with each finite adelic translation:

`S.horizontalDifferential q (S.horizontalFiniteRepresentation q d f) =
  S.horizontalFiniteRepresentation (q + 1) d (S.horizontalDifferential q f)`.

The horizontal cochains are the existing full-compact-equivariant alternating
maps on the actual reduced complex Lie algebra, vanishing whenever an argument
belongs to the compact image. Both the differential and finite action are the
previously constructed operators on these exact spaces. Subtype extensionality
reduces the equation to the published coefficient `map_differential` theorem,
applied to `S.finiteReducedLieHom d`. That Lie-module map is the same finite
translation, whose reduced Lie commutation was already proved.

`horizontalDifferentialIntertwiner q` bundles this same differential as an
intertwiner from the degree-`q` finite representation to the degree-`q+1` finite
representation. Its intertwining equation is the preceding commutation theorem
by linear-map extensionality. Its underlying-linear-map theorem is a definitional
equality to `S.horizontalDifferential q`.

This internal construction reuses `HorizontalFiniteAction`, the actual
`HorizontalDifferential`, and `CoefficientCochains.map_differential`.
No additional covariance or infinitesimal compatibility hypothesis is supplied,
and no external identification is asserted. This module does not prove square
zero, construct cycles, boundaries or cohomology, assert continuity or smoothness
of the entire horizontal finite representation, or attach general tensor
coefficients.

Implementation note. The local `AddCommGroup` instances on
`RationalInvariantFunctions F n`, `ContinuousRationalFunctions F n`,
`FiniteSmoothRationalFunctions F n`, `AutomorphicForms F n`,
`StableAutomorphicFunctions F n` and `S.Space` are exactly the canonical
`Submodule.addCommGroup` structures and remain local to this module. They
have explicit names with the prefix `horizontalDifferentialFinite`. Anonymous
instances would receive generated public declaration names coinciding with
those of `HorizontalCohomology` or `HorizontalCohomologyClasses`; the
explicit names permit importing this module together with both of those
modules, in either order. No construction or theorem changes.

Authorship: Worker 2. Import-collision correction (explicit local instance
names): Worker 986.
