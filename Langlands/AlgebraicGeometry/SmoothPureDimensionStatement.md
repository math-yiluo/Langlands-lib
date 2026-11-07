# Smooth chart dimension and pure dimension of actual fibres

This derived statement supplies a geometric comparison needed in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.12, the third proof paragraph of Theorem 4.5.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
That paragraph passes to target components and enlarges the arithmetic
set to obtain a common dimension for the smooth geometrically connected
nonempty fibres. The present target compares the standard-smooth chart
predicate used by Mathlib with the Library's actual componentwise
dimension predicate. It is an internal prerequisite, not the arithmetic
spreading assertion in that paragraph.

`FieldSmoothPureDimensionStatement` says that an actual scheme `X` smooth
of standard-smooth relative chart dimension `n` over any field `k` has
pure dimension `n`. The imported `SchemeFiberGeometry.HasPureDimension`
means that every actual topological irreducible component has
topological Krull dimension `n`; it does not mean only that the supremum
of component dimensions is `n`.

`SmoothPureDimensionFibersStatement` gives the corresponding assertion
for any scheme morphism `f : X ⟶ Y` smooth of fixed chart dimension `n`.
It uses `f.fiber y`, the actual scheme pullback along
`Spec κ(y) ⟶ Y`, for every point `y` of the target. Thus its conclusion is
the published `SchemeFiberGeometry.HasPureDimensionFibers n f`.

Both targets allow arbitrary schemes in common universe `u`, with no
affineness, separatedness, quasi-compactness, geometric connectedness or
surjectivity hypothesis. Smoothness already gives local finite type.
Pure dimension is vacuous on an empty scheme or empty fibre. In
particular these targets assert no nonemptiness.
`SmoothPureDimensionStatement` is exactly the conjunction of these two
Prop-valued targets.

The provenance is derived: the planned comparison uses the published
closed-point stalk dimension and quasi-compact smooth dimension bound,
then affine neighbourhoods and the published equivalence between pure
dimension and constant local topological dimension for locally
finite-type field schemes. Base change of the fixed smooth chart
dimension supplies the actual-fibre assertion. This file only states
the comparison. Its proof, compatible arithmetic spreading, uniform
Lang–Weil and the final adelic openness theorem remain separate
obligations.
