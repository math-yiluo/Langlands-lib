# Hom representation for the coherent-family images of line bundles

For a flat morphism `f : X → S`, an arbitrary scheme `T` over `S`,
and actual line bundles `L, M` on `T ×_S X`,
`PicardGroupoid.relativeFamilyHomIntrinsicIso` identifies the full
coherent-family Hom presheaf between their images under
`relativeToFamily f T` with the intrinsic ordinary-module Hom presheaf
of `L.of.obj` and `M.of.obj` for the relative projection.

This is an internal consumer adapter. Its construction specializes the
published `CoherentSheaves.FamilyGroupoid.homPresheafIntrinsicIso`;
the image families' underlying module sheaves are definitionally the
original ones. The natural isomorphism therefore retains all module
maps and coherent restrictions on the entire slice `Over T.left`.
Flatness is needed by the line-bundle-to-family inclusion. Properness
and local finite presentation are not needed for this comparison.

`relativeFamilyHomRepresentable_iff` transports affine locally finitely
presented scheme representation in either direction along that
natural isomorphism, using the published `of_iso` lemma. This
transport preserves the representing scheme and its structure morphism.

`relativeFamilyHomRepresentable_of_properLineBundleHomRepresentability`
additionally assumes properness and local finite presentation of `f`,
and a proof of `ProperLineBundleHomRepresentabilityStatement.{u}`.
It applies that proof to the original two line bundles and then
transports the resulting representation to their image families.
It can be applied to each of the four pairs
`(L,M)`, `(M,L)`, `(L,L)`, and `(M,M)` in the inverse-equation
construction of Isom schemes.

All declarations preserve universe `u`, arbitrary bases and parameter
schemes, and the full test slice. The last theorem is conditional on
the focused Hom result. This module supplies no unconditional Hom
proof, no Isom representation, and no Picard atlas.
