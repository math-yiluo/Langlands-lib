# Smooth direct image along continuous equivariant maps

This is an internal construction from the ordinary equivariant direct image in
`DirectImage.lean` and the smooth-sheaf coreflector in `SmoothPart.lean`. It gives
actual functors, maps and coherence laws in the existing categories of sheaves.
It is a general topological prerequisite for the Harris framework; it asserts no
analytic or étale realization or arithmetic specialization.

## Scope and construction

The coefficient ring `R` is commutative. The group `G` is a topological group,
and the spaces carry `G`-actions with continuous individual translations and
`HasStableNeighbourhoods`: every open neighborhood of each point contains an
open neighborhood stable under an open subgroup. The ring, group, spaces and
module carriers share a universe `u`. A spatial map `f : C(X, Y)` is supplied
with its equivariance equation. No properness condition is needed here.

`SmoothTopologicalSheaf R G X` is the existing full subcategory of ordinary-open
equivariant module sheaves satisfying local smoothness. For a smooth sheaf `F`,
`functor f hf` first includes `F` into all equivariant sheaves, then takes the
ordinary direct image along `f`, and then applies `smoothCoreflector R` on `Y`.
Thus the sections over an ordinary open `U` are precisely the sections of `F`
over `f⁻¹(U)` that are locally fixed at every point of `U` in the direct-image
transport sheaf. This last condition is measured on `Y` using the existing
`smoothSubmodule`; it is not a condition silently inferred from smoothness on
`X`. The imported smooth-part construction proves that these submodules form
an actual equivariant sheaf and that this sheaf is smooth.

`additive` proves that this functor preserves addition of sheaf morphisms.
The natural transformation `inclusion` includes the smooth direct image into
the full ordinary direct image. Each component is a monomorphism by the existing
smooth-subsheaf inclusion. `inclusion_apply` identifies it with subtype inclusion.
`map_apply` says that a morphism is evaluated on its original inverse-image-open
component and restricted to the locally smooth sections.

## Universal property

For smooth sheaves `F` on `X` and `K` on `Y`, `homEquiv f hf F K` is the
bijection

```text
Hom(K, smoothDirectImage_f(F)) ≃ Hom(K.obj, ordinaryDirectImage_f(F.obj)).
```

It is the inverse of the Hom equivalence for the published adjunction between
smooth inclusion and smooth coreflector. `lift` is its inverse applied to a
map into ordinary direct image. `lift_inclusion` proves that composing with the
actual inclusion recovers the supplied map; `hom_ext` gives uniqueness.
`lift_apply` says that the underlying section is the section supplied by that
map. These constructions do not take a smooth direct-image preservation theorem
as input.

## Identity and composition

`idIso` is the adjunction unit, oriented from the identity on smooth sheaves to
smooth direct image along the identity spatial map. The inclusion of the full
smooth subcategory is fully faithful, so its adjunction unit is invertible.
`idIso_hom_apply` states that its underlying section is the original section.

For `f : X → Y` and `g : Y → Z`, `compMap f hf g hg` is a natural transformation
from iterated smooth direct image, first along `f` and then along `g`, to smooth
direct image along `g ∘ f`. Its map into the full ordinary direct image is the
smooth inclusion for `g`, followed by ordinary direct image along `g` of the
smooth inclusion for `f`. The full ordinary composite is definitionally the
direct image along the composite continuous map. The universal property above
factors this composite through its smooth part. `compMap_inclusion` states the
resulting square, and `compMap_apply` states that the underlying section is
obtained by forgetting the two iterated smoothness proofs.

`compMap_id_left` and `compMap_id_right` prove the two unit equations, inserting
the displayed identity unit before or after the spatial map. `compMap_assoc`
proves equality of the two maps from three iterated smooth images to the image
along their composite. The proofs compare the actual sheaf maps on sections;
after subtype extensionality each equation is reflexivity. These are coherent
lax composition maps; no assertion that `compMap` is invertible is made.

## Provenance and remaining obligations

All new objects are compositions or universal factorizations of the imported
concrete functors. The identity isomorphism uses Mathlib's fully faithful
adjunction result. The remaining intrinsic equations are proved on the original
module sections. No new existence assumption, axiom, or higher comparison is
introduced. This unit does not establish exactness, preservation of local
smoothness by ordinary direct image, comparison of Godement resolutions,
derived-functor identities, or compact-support and arithmetic realizations.
