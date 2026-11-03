# Morphism properties of representations over an open base cover

This is an internal categorical and locality consequence of
`SchemeBaseChange`, `LocalRepresentationGluing`, the full faithfulness of
lifted Yoneda, and Mathlib's API for properties local for the Zariski topology
on the target. It provides no additional geometric existence assumption.

Fix a scheme `B` in universe `u` and a presheaf `F` on the entire slice
`Over B` with values in `Type (u + 1)`.
`LocalRepresentation.localRepresentativeIso` takes an arbitrary morphism
`j : U ⟶ B`, a global representative `V : Over B` of `F`, and a representative
`H : Over U` of the restriction of `F` along `Over.map j`. It constructs an
isomorphism in `Over U` from the actual base change `(Over.pullback j).obj V`
to `H`. First `representedBaseChangeIso` identifies the represented presheaf
of that base change with the restriction of `F`. Composing with the inverse
of the local representation yields an isomorphism between two represented
presheaves. Full faithfulness of lifted Yoneda lifts it to the claimed
isomorphism of actual schemes over `U`. No openness premise is needed here.

`property_of_local_representations` assumes that a morphism property `P` is
local for the Zariski topology on its target, a global representative `V`,
and local representatives `H i` over an open base cover indexed in `Type u`.
If `P` holds for each structure map `(H i).hom`, it holds for `V.hom`.
Mathlib's `IsZariskiLocalAtTarget.of_openCover` reduces the conclusion to the
maps from the actual pullbacks to the cover members. The preceding
isomorphism identifies each pullback with `H i` in the slice; its slice
commutativity equation expresses the pullback structure map as the
isomorphism followed by `(H i).hom`. Invariance of `P` under composition
with an isomorphism proves the required property.

`exists_affine_representation` additionally assumes that `F` is an fppf
sheaf and has full-slice representatives over an open cover, each with an
affine locally finitely presented structure map. It first uses
`LocalRepresentation.exists_representation` to obtain an actual global
representative. It applies `property_of_local_representations` twice, for
`IsAffineHom` and for `LocallyOfFinitePresentation`, to that same
representative and its same structure map. The conclusion is an object
`V : Over B`, a natural isomorphism from its lifted represented presheaf
to `F`, and both properties of `V.hom`.

All comparisons remain natural on arbitrary test schemes and arbitrary
slice arrows. The sheaf premise and local representatives remain explicit
assumptions; this module does not prove their existence for the actual
proper coherent-family Hom presheaf.
