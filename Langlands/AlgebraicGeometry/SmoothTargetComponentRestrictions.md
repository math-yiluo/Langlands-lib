# Smooth restrictions over actual target components

This derived construction implements the connected-component step used in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.12, Theorem 4.5 proof, third paragraph. The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
That paragraph passes to target components and enlarges the finite arithmetic
set to obtain common fibre dimensions. This module constructs the component
restrictions and their standard-smooth chart dimensions. It does not carry out
the arithmetic enlargement or identify chart dimension with pure fibre
dimension.

## Actual restrictions and covers

For an actual scheme map `f : X ⟶ Y` with locally Noetherian target, the index is
Mathlib's actual topological quotient `ConnectedComponents Y`.
The published `componentOpen Y c` is the open subset of points in component
`c`, with its full open scheme structure `componentScheme Y c`.
`componentPreimageOpen f c` is its inverse image in `X`, and
`componentPreimageScheme f c` is the corresponding actual open subscheme.
No affineness, reduction, field or separatedness assumption is imposed.

`targetComponentRestriction f c` is Mathlib's scheme restriction `f ∣_ U`.
Its inclusion square commutes and is a scheme pullback. The inverse-image
opens are pairwise disjoint and have supremum the whole source;
`componentPreimageOpenCover f` constructs their actual open cover. Together
with the imported `componentOpenCover Y`, the two covers share the same
component index, and their maps commute with the original morphism.

`finite_componentIndex_of_compact` proves that this index is finite when `Y`
is compact. The actual quotient map onto components is a quotient map.
The preimage of each singleton is `componentOpen Y c`, hence open.
The quotient topology is therefore discrete. It is also compact as a
continuous quotient of `Y`, and compact discrete spaces are finite.
This proof needs no assumed `LocallyConnectedSpace` instance.

All cover and index assertions include the empty case. If `Y` is empty,
the component index is empty, as already proved by the imported
`componentIndex_isEmpty`. A morphism to `Y` then also has empty source;
the constructed source cover is the empty cover.

## Selected chart dimensions

Suppose additionally that `f` is smooth and geometrically connected, in
Mathlib's sense that all its field-valued base changes have connected
nonempty source. Both properties persist under the actual pullback
restriction. Each target component scheme is connected and nonempty.
Smooth maps are open, so Mathlib's
`GeometricallyConnected.connectedSpace` shows that every source
restriction is connected and nonempty.

`smoothTargetComponentDimensions f` selects one natural number for each
component by applying the published
`smoothConnectedRelativeDimension` to its actual restricted morphism.
`smoothTargetComponentDimensions_spec` proves
`SmoothOfRelativeDimension (smoothTargetComponentDimensions f c)
(targetComponentRestriction f c)`.
Standard-smooth charts of the selected fixed dimension therefore exist
around every source point of each actual restriction. The number may vary between components;
no global common dimension or uniqueness is asserted.

The implemented argument reuses published component schemes and the
published connected-source relative-dimension theorem. Its new construction
consists of the actual inverse-image family, restriction squares, paired
cover, finite-index argument and selected dimension function with its
intrinsic specification. It works in arbitrary common universe `u`.

## Remaining boundary

The dimension in this module is Mathlib's standard-smooth chart predicate.
The bridge to `SchemeFiberGeometry.HasPureDimension` on the actual residue
fibres remains a separate obligation. Compatible spreading, enlargement of
the arithmetic set, uniform Lang–Weil, almost-all integral surjectivity and
the final adelic openness theorem also remain separate obligations.
