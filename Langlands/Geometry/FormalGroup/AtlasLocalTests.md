# Universal localization tests for formal coordinate atlases

This derived unit gives canonical localized coordinates for every point of a
`ModuleLaw.BasicAtlas`. It constructs one universal chart test per chart,
factors every other test through it, and proves that equality at these canonical
tests detects equality of atlas points. The resulting coordinate map is an
injective O-linear map into a product of actual nilpotent chart-point modules.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
obtained by gluing formal groups over base localizations. The registered source
is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present result is an internal consequence of the localization universal
property and the compatible-family construction in `BasicAtlas`, motivated by
that convention. It is not an additional numbered assertion of the source.

The base R is an arbitrary commutative O-algebra. The finite coordinate type σ
is fixed, and coefficient test algebras have the same universe v as R. The atlas
point module retains universe v+1. The proofs do not require using the cover's
span condition or its transition equations: coefficient naturality alone
already determines each component of a compatible family from its universal
localized component. Thus this unit proves detection of points, without
claiming that every family of localized tuples glues. An image characterization,
explicit overlap descent, refinement comparisons, formal-scheme comparison,
order actions, moduli objects and representability remain further work.

## Canonical tests and factorization

For an R-algebra A and a chart element a, `localAlgebra A a` is the actual
localization of A at the image of a, viewed as an R-algebra. `localizationMap`
is its structural A-algebra map, restricted to R-algebras. `localUnit` proves
that a is a unit there, using the scalar-tower identity and the defining unit
property of localization. `localTest` packages this algebra, structural map,
chart and unit proof as a `ChartTest A`.

For an arbitrary test t, its map A → B sends the chosen chart element to a unit
in B. `testFactor t` is the localization lift A[1/a] → B, as an R-algebra map.
`localizationMap_testFactor` proves that its composite with the structural
localization map equals t's original map. The proof evaluates the lift on each
original coefficient and applies `IsLocalization.Away.lift_eq`.

## Detection and the linear coordinate map

`component_from_localTest` applies the compatible family's coefficient
naturality equation to this factorization. It says that applying the actual
O-linear chart-point coefficient map along `testFactor` to the canonical tuple
recovers the tuple at t. The equality of composite test maps is transported
through family evaluation; all tuple operations are those of the localized
formal chart law.

`ext_localTests` proves equality of two atlas points by equality of their
canonical tuples in every chart. Subtype and function extensionality reduce
the goal to an arbitrary test; the preceding component formula rewrites both
sides as the same coefficient map applied to the equal canonical tuples.

`localizedCoordinates A` collects the evaluations at `localTest A a` for all
charts a. The codomain is the dependent product of those actual chart-point
O-modules. Its O-linearity is componentwise linearity of evaluation, which is
definitional in the compatible solution submodule. The local chart module
instances explicitly reuse the corresponding `BasicAtlas` instances.
`localizedCoordinates_injective` applies `ext_localTests` to the pointwise
consequences of equality of these dependent functions.
