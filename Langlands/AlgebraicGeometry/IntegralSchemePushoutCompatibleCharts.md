# Compatible open charts in locally ringed pushouts

This internal helper specializes the cartesian-open-colimit criterion to
pushout spans, and then to restrictions of a span of schemes to compatible
open subsets. All spaces and schemes have an arbitrary common universe `u`.
It does not assume that the large locally ringed pushout is a scheme.

## Two locally ringed pushouts

`LocallyRingedPushout.isOpenImmersion_and_range` takes two actual pushout
squares of locally ringed spaces, and a map between their spans given by open
immersions `z`, `l`, and `r`. The two squares in the map of spans must commute.
The inverse images of the ranges of `l` and `r` along the large span maps
must both equal the range of `z`. A map `q` between the pushout points must
commute with the two outer cocone legs.

The conclusion is that `q` is an open immersion and that its inverse images
under the two large cocone legs are exactly the ranges of `l` and `r`.
The proof constructs the natural transformation with `spanHomMk`. The two
cartesian hypotheses give the cartesian condition on its nonidentity arrows;
identity arrows require no additional hypothesis. It then applies the earlier
locally ringed colimit criterion and range lemma. Mathlib supplies colimits
and preservation for this finite indexing category.

## Compatible scheme opens

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be scheme maps, and let `U` and `V` be open
subsets satisfying `i ⁻¹ᵁ U = j ⁻¹ᵁ V`. `CompatibleOpen.leftMap` and
`CompatibleOpen.rightMap` are the restricted maps from the scheme of the
common inverse image to the schemes of `U` and `V`, using `Scheme.Hom.resLE`.

`CompatibleOpen.comparison` takes a locally ringed pushout of this restricted
span and a locally ringed pushout of the original span. It constructs the
map between their points by the small pushout universal property. The needed
commutativity follows from `resLE_comp_ι` and the large pushout square.

`CompatibleOpen.comparison_isOpenImmersion_and_range` proves that this map
is an open immersion and that its inverse images along the large legs are
exactly `U` and `V` as sets. The preceding two-pushout criterion applies to
the inclusions of the three open subschemes. Their ranges are the prescribed
open sets by `Scheme.Opens.range_ι`, and compatibility supplies the second
cartesian range equality.

These are derived consequences of the preceding project colimit helpers and
Mathlib's pushout and scheme-restriction APIs; no additional literature result
is asserted. The statements do not require the opens to be affine. Constructing
suitable affine open pairs, the affine pushout, a scheme structure on the
large pushout, and the final integral and closed-immersion properties remain
separate obligations.
