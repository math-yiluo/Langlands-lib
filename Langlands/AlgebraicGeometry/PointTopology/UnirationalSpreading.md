# Spreading out local parametrizations of unirational schemes

Author: Worker 1420.

This is an internal, derived interface for the actual scheme predicate
`PointTopology.IsUnirational` from `UnirationalDensity`. The field `k` and
all schemes have arbitrary universe `u`. There is no infinitude, perfection
or characteristic assumption on `k`.

`isUnirational_affineSpace ι` proves that the actual affine space
`𝔸(ι; Spec k)`, for a finite coordinate type `ι`, is unirational over `k`.
The witness is the top open subscheme with its inclusion. The top open is
nonempty because affine space surjects onto the nonempty scheme `Spec k`, and
its inclusion has dense range because it is dense open.

`IsUnirational.of_open_denseRange` takes a unirational `Y` over `k`, a
nonempty open subscheme `V` of `Y`, and an actual morphism `f : V → X` over
`k` (the equation `f ≫ X.hom = V.ι ≫ Y.hom`) with dense underlying range. It
proves that `X` is unirational. From the parametrization `p : U → Y` of `Y`,
with `U` an open of affine space, the proof takes the preimage `W` of `V`
in `U`. `W` is nonempty because `p` has dense range and `V` is a nonempty
open. The image of `W` in affine space is again an open subscheme. The new
parametrization is the inverse of the isomorphism from `W` onto that image,
followed by the restriction `p ∣_ V` and then `f`. The restriction of a
dominant morphism to the preimage of an open is dominant, because dominance
is local on the target. Composition of dominant morphisms gives dense range.

`IsUnirational.of_stalk` takes a unirational `Y` over `k`, a point `y` of `Y`
at which the germ maps of `Y` are injective (`IsGermInjectiveAt`), a target
`X` locally of finite type over `k`, and an actual morphism
`φ : Spec 𝒪_{Y,y} → X` compatible with the maps to `Spec k` and having dense
range. It proves that `X` is unirational. Mathlib's
`spread_out_of_isGermInjective'` spreads `φ` out to a morphism `f : V → X`
over `k` on an open neighborhood `V` of `y`, with `φ` equal to the canonical
map `Spec 𝒪_{Y,y} → V` followed by `f`. Hence the range of `φ` is contained
in the range of `f`, so `f` has dense range, and
`IsUnirational.of_open_denseRange` applies.

`IsUnirational.of_affineSpace_stalk` specializes `of_stalk` to `Y` equal to
the affine space `𝔸(ι; Spec k)` for a finite coordinate type `ι`, using
`isUnirational_affineSpace`. Mathlib's instances give germ injectivity of
affine space at every point, so `x` may be any point of affine space, for
example its generic point. Thus a morphism over `k` from the spectrum of the
local ring of affine space at `x` with dense image in `X` makes `X`
unirational. With `x` the generic point, that local ring is the rational
function field `k(x_i : i ∈ ι)`, whose spectrum is one point, so the density
hypothesis says that the image of this point is dense in `X`.

`HasDenseRationalFunctionFieldPoint k X` is the proposition that, for some
finite coordinate type `ι : Type u`, there is an actual morphism
`φ : Spec k(𝔸^ι) → X`, where `k(𝔸^ι)` is Mathlib's function field of
`𝔸(ι; Spec k)` (the local ring at its generic point). `φ` must be compatible
with the maps to `Spec k`. That is, `φ ≫ X.hom` equals the canonical map from
the function field's spectrum to affine space followed by the structure map.
Its underlying range must be dense in `X`. The coordinate type is explicitly
finite. `HasDenseRationalFunctionFieldPoint.isUnirational` proves that such a
point makes `X` unirational when `X` is locally of finite type over `k`. It is
`IsUnirational.of_affineSpace_stalk` at the generic point. Spec of a field has
one point, so density says that the image of that point is dense in `X`.

The provenance is the published `UnirationalDensity` definition and the
pinned Mathlib modules `AlgebraicGeometry.SpreadingOut`,
`AlgebraicGeometry.Morphisms.UnderlyingMap` and
`AlgebraicGeometry.Restrict`, together with elementary topology of dense
ranges. No external structural theorem is asserted. This module does not
prove that any maximal-torus parameter scheme is unirational. It supplies
the spreading-out step by which a point over a purely transcendental
function field gives an actual affine-open parametrization.
