# Scheme representations of actual point fibres

This internal construction applies to the actual pseudofunctor and slice
conventions of `Stacks.SchemeAtlas`. The base `S` is any scheme, and `F`
is a contravariant pseudofunctor on `Over S` whose fibre categories are
groupoids. Fix `ξ` over `U` and `η` over `T`. All declarations preserve
the scheme universe `u`; presheaves take values in `Type (u + 1)`.

`productHomPresheaf F ξ η` is the Hom presheaf of the two projection
pullbacks on the product `U × T` in `Over S`, reindexed along the
iterated-slice equivalence to all schemes over its underlying scheme.
An input representation consists of an actual `I : Over (U × T).left`
and a natural isomorphism from its lifted scheme Yoneda presheaf to
this product Hom presheaf.

`pointFiberScheme I` is the same actual scheme with structure map
`I.hom ≫ prod.snd.left` to `T.left`. `pointFiberRepresentation` supplies
its `RepresentableBy` data for `Stacks.pointFiberPresheaf F ξ η`, and
`pointFiberSchemeIso` packages those data as the natural isomorphism
from its scheme Yoneda presheaf to that entire point-fibre presheaf.
This includes every test scheme and every slice restriction morphism.

The construction proceeds through four already-defined comparisons.
First, `RepresentableBy.ofEquivalence` transports the supplied product
Hom representation from schemes over the underlying product to the
iterated slice. Second, `SlicePresheafTotal.representationIso` composes
that representing object's map with the second projection. Third,
`PointFiberProduct.presheafIso` identifies the resulting total presheaf
with the actual point-fibre presheaf. Finally, the adjunction of the
iterated-slice equivalence transports the representation to schemes
over `T.left`. Its naturality follows from adjunction naturality and
the preceding representation's composition law. The resulting underlying
scheme and map are definitionally those of `pointFiberScheme I`.

The provenance is internal categorical infrastructure: composition of
actual slice maps, transport of representations through an equivalence,
and the previously constructed natural point-fibre comparison. No
external geometric theorem is invoked. This unit requires a supplied
representation of the product Hom presheaf; it does not assert that
such representations exist. It supplies no smoothness, surjectivity,
local finite type condition, or atlas existence.
