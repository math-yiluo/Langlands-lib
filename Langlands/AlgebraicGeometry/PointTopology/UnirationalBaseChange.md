# Actual unirational parametrizations after field extension

Author: Worker 1630.

This derived helper extends an actual affine-open parametrization along
an arbitrary field extension `k → K`. It uses the published
`PointTopology.IsUnirational` predicate without adding a reducedness,
finite-type, separability, perfection, or infinitude assumption. All
schemes, fields and coordinate types live in one arbitrary universe `u`.

`denseRange_of_isPullback_of_isOpenMap` is a general scheme statement.
For a Cartesian square `IsPullback pX pY f g`, if `f` has dense image and
`g` is an open map, then `pY` has dense image. The proof uses Mathlib's
scheme-pullback image identity: the image of `pY` is the inverse image
under `g` of the image of `f`. An open map pulls dense sets back to dense
sets.

For a coordinate type `ι`, an open `U` of affine space over `k`, and a
morphism `f` over `k` from `U` (with its structure map to `Spec k`) to `X`,
`affineOpenBaseChangeMap` is an actual morphism over `K`. Its source is
the inverse image of `U` under the affine-space scalar-extension map
`𝔸(ι; Spec K) → 𝔸(ι; Spec k)`, with its structure map to `Spec K`. Its
target is the pullback of `X` along `Spec K → Spec k`. The map into this
pullback has two components. The first is the restricted scalar-extension
map followed by `f`. The second is the structure map to `Spec K`.

`isPullback_affineOpenBaseChangeMap` states that this square is
Cartesian. Its other sides are the restricted scalar-extension map,
`f`, and the first projection from the pullback of `X` to `X`. To prove
it, the restriction square for `U` is pasted with Mathlib's affine-space
pullback square. This gives a Cartesian square over `Spec K → Spec k`. The
square is then cancelled against the defining pullback square of the
pullback of `X`.

`denseRange_affineOpenBaseChangeMap` applies the general lemma to this
square. The required open map is the projection from the pullback of
`X` to `X`. Mathlib proves that every scheme morphism to the spectrum of
a field is universally open. Hence this projection is open for every
field extension.

`IsUnirational.baseChange` keeps the same finite coordinate type. The
inverse-image open is nonempty because the affine-space scalar-extension
map is surjective. It is the base change of the surjective map
`Spec K → Spec k`, which is surjective because `Spec K` is nonempty and
`Spec k` has one point. The constructed morphism has dense image by the
preceding lemma. This gives exactly the actual affine-open witness
required by the existing predicate over `K`, for the pullback of `X`
along `Spec K → Spec k`.

The provenance is internal and derived from Mathlib's scheme pullback,
restriction, universal-openness, and affine-space interfaces. No external
theorem is asserted. This module does not construct a parametrization for
maximal-torus parameter schemes; it supplies transport once such a
parametrization is available.
