# Global smooth Godement maps for full coefficients and support comparison

This module constructs global chain and cohomology pullbacks for the full
locally constant smooth coefficient sheaves. For proper maps it proves
that the existing compact pullbacks commute with forgetting support.
It combines the actual coefficient maps from
`SmoothDirectImage/Coefficients` with the global spatial maps from
`SmoothGodement/SupportComparison`. Compact maps are those already
constructed in `SmoothGodement/CoefficientSpatial`.

The commutative ring `R`, topological group `G`, spaces and representation
carriers share universe `u`. The spaces have `G` actions, continuous fixed
translations and `HasStableNeighbourhoods`. A map `f : C(X, Y)` is
continuous and equivariant. The global maps do not require properness.
The compact-to-global comparisons explicitly assume `IsProperMap f`.
Coefficients range over every object and original intertwiner of
`SmoothRep R G`; no coefficient-module topology or finite-dimensionality
condition is imposed.

Let `L_X` be `LocallyConstantSheaf.smoothFunctor R G X`, let `A_X` be
`smoothGodementGlobalComplex R G X`, and let `D_f` be smooth direct image.
These are ordinary-open equivariant sheaves and the separate smooth
Godement complex. The global section complex takes values in algebraic
representations `Rep R G`, without a smoothness restriction on global
sections.

`coefficientGlobalNatTrans f hf` is the transformation
`L_Y ⋙ A_Y ⟶ L_X ⋙ A_X` whose component at `M` is

```text
A_Y.map(SmoothDirectImage.coefficientMap f hf M)
  ≫ globalMap f hf (L_X.obj M).
```

It first resolves the full coefficient sheaf map and then applies the
constructed global spatial chain map. The component equation is
`coefficientGlobalNatTrans_app`. The original-section equation
`coefficientGlobalNatTrans_apply` holds in every chain degree: apply the
resolved coefficient map, then the degreewise smooth Godement spatial
sheaf map at the top open, and remove its smooth-image subtype witness.
Higher Godement sections are not identified with original locally
constant coefficient functions.

The coefficient naturality theorem is the commuting square for every
original intertwiner. The identity theorem uses
`SmoothDirectImage.coefficientMap_id` to identify the coefficient map
with the actual direct-image unit, followed by `globalMap_id`.
For composition, `coefficientGlobalNatTrans_comp` expands the coefficient
composition equation. Its final lax comparison is exactly the one in
`globalMap_comp`; the latter equation and spatial naturality then give
strict contravariant composition

```text
pullback(g.comp f) = pullback(g) ≫ pullback(f).
```

No inverse to the lax direct-image comparison is assumed.
`coefficientGlobalNatTrans_congr` substitutes equality of the original
continuous maps; proof irrelevance reconciles equivariance witnesses.

For a proper map, `coefficientCompactNatTrans_forgetSupport` states the
chain square at every `M`. Its left side applies the inclusion
`SmoothRep.toRep` degreewise to the full-coefficient compact pullback,
then the original compact-support inclusion on `X`. Its right side first
forgets support on `Y`, then applies the coefficient global pullback.
The proof expands both coefficient maps, applies
`compactMap_forgetSupport` from `SupportComparison`, and moves the
coefficient sheaf map through support forgetting by naturality.
Thus the square compares the actual original support inclusions.

`coefficientGlobalCohomologyNatTrans f hf q` applies homology in
`Rep R G` in nonnegative degree `q` to the global chain transformation.
Its components are homology of the constructed chain maps, as recorded
by `coefficientGlobalCohomologyNatTrans_app`. The alternative component
formula `coefficientGlobalCohomologyNatTrans_app_eq` factors through
the coefficient sheaf map and the existing global cohomology spatial
map. The transformation retains all coefficient intertwiners. Its
identity and strict composition laws follow by applying homology to
the corresponding chain equations.

`coefficientCohomologyNatTrans_app_eq` gives the analogous factorization
of the existing compact cohomology transformation. Using these two
factorizations, `coefficientCohomologyNatTrans_forgetSupport` proves
the cohomology square: include smooth compact cohomology in algebraic
representations and then forget support on `X`, or forget support on
`Y` and then apply global cohomology pullback. The proof applies the
already established `cohomologyMap_forgetSupport` and naturality of
`forgetSupport` at the coefficient sheaf map. The imported support
transformation uses the inverse of the proved exact-inclusion homology
comparison for `SmoothRep.toRep`, followed by homology of the chain
inclusion. This is the precise comparison used here; smooth compact
homology and algebraic global homology are not silently identified.

The provenance is internal: all objects and maps are composites of the
imported coefficient sheaf maps, actual smooth Godement spatial maps,
support inclusions and categorical homology. The intrinsic equations
follow from their proved functoriality and naturality. No new external
literature assertion is attributed to this module.

This construction does not prove Godement resolution exactness,
acyclicity, identification with higher right derived functors, invariants
commuting with homology, comparison with the full equivariant Godement
route, degree-zero compatibility with separately transported maps, or
analytic, etale, uniformization, Shimura or Harris realization. Those
remain separate obligations of the broader framework.
