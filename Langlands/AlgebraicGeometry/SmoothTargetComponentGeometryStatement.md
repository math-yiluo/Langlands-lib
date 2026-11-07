# Full fibre geometry on actual target-component restrictions

This derived statement supplies the pure-dimension step in the proof of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.12, Theorem 4.5, third proof paragraph.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paragraph passes to connected components of the field target before
enlarging the arithmetic set to arrange a fixed fibre dimension.

## Actual fibres and selected dimensions

`SmoothTargetComponentFiberGeometryStatement` quantifies arbitrary schemes
`X`, `Y` in a common universe, with `Y` locally Noetherian, and a smooth
geometrically connected morphism `f : X ⟶ Y`. For every actual topological
connected component `c` of `Y`, it asserts
`NonemptyGeometricallyConnectedPureDimensionFibers
(smoothTargetComponentDimensions f c) (targetComponentRestriction f c)`.

All constructions are the existing published ones. The target is the full
open subscheme on component `c`; the source is its actual inverse image
in `X`; the restriction square is a scheme pullback. The selected natural
number is the standard-smooth chart dimension already constructed in
`SmoothTargetComponentRestrictions`. This statement identifies that
particular selected number with the pure dimension of every actual
residue-field fibre of the restriction.

The fibre predicate is the published `SchemeFiberGeometry` predicate:
each fibre is nonempty, its structure morphism to the target residue
field is geometrically connected, and every irreducible component with
its subspace topology has topological Krull dimension equal to the
selected natural number. There is no replacement by an affine or reduced
scheme, no supplied fibre isomorphism and no dimension assumption.
Geometric connectedness is Mathlib's field-base-change property, which
includes nonemptiness. The selected dimension may differ between target
components. An empty target gives an empty component index.

This clause does not assume compactness, separatedness or a chosen base
field. It is a derived geometric extension of the component step in
Conrad's finite-type field setting. When `Y` is compact, the existing
`finite_componentIndex_of_compact` makes its component index finite.

## Preservation over the original base

`TargetComponentFiniteTypeSeparatedStatement` is a separate preservation
clause. Given locally Noetherian `X` and `Y`, any scheme `B`, and
finite-type separated structure maps `p : X ⟶ B` and `q : Y ⟶ B`,
both actual restricted structure maps remain finite type and separated:
the source structure map is `componentPreimageι f c ≫ p` and the target
structure map is `componentι Y c ≫ q`.

Here finite type is expressed as locally of finite type and
quasi-compact. No smoothness or geometric connectedness of `f` is needed
for this clause, and no compatibility equation between `p`, `q` and `f`
is assumed or concluded. If `f` is over `B`, its published restriction
square supplies the inherited compatibility. Local Noetherianity of
the source is explicit; in the smooth setting of the first clause it
follows from local Noetherianity of the target and local finite type.
The clause covers nonaffine and empty schemes.

`SmoothTargetComponentGeometryStatement` is the conjunction of these
two targets for arbitrary common universe `u`.

## Derivation and remaining boundary

The first clause is obtained from the existing
`smoothTargetComponentDimensions_spec` by the fixed smooth-chart to
pure-fibre-dimension comparison in `SmoothPureDimensionStatement`, and
from base-change preservation of geometric connectedness. The second
uses the actual open inclusions: they are locally of finite type and
separated, and are quasi-compact because their targets are locally
Noetherian. Composition then preserves all three properties.

This unit states those results. It does not prove them, choose arithmetic
models, enlarge a place set, make the dimensions equal across distinct
components, prove Lang–Weil, or prove adelic openness. Compatible model
existence and the remaining arithmetic and topological arguments are
separate obligations.
