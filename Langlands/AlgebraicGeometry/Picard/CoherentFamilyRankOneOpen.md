# The line-bundle open of an actual coherent family

This is an internal specialization of the full-fibre rank-one open and its
cartesian base-change criterion to the published actual coherent-family
groupoid. The schemes have arbitrary universe `u`. No restriction is imposed
on the schemes or morphisms of the full slice.

For a flat structure map `p`, `PicardGroupoid.toFamily_essImage_iff` identifies
the essential image of the actual line-bundle inclusion with local freeness
of rank one of the underlying module. In one direction an actual family-core
isomorphism transports local trivializations. In the other direction the same
module with the supplied local trivializations is a line bundle, and its
inclusion has an actual identity module isomorphism to the original family.
`relativeToFamily_essImage_iff` applies this criterion to each relative space,
whose projection is flat by base change.

Fix a universally closed `f : X ⟶ S`, a test `T : Over S`, and an actual
`M : CoherentSheaves.FamilyGroupoid f T`. Its module is locally finitely
presented and flat over the actual projection to `T.left`.
`familyRankOneOpen f M` is the full-fibre rank-one open for that projection.
Universal closedness of the projection follows from base change.
`familyRankOneBase` retains this open as a scheme over `S`, and
`familyRankOneInclusion` is its actual open inclusion into `T`.

The commuting relative-space square shows directly that the ordinary pullback
of `M` along this inclusion is locally free of rank one.
`familyRankOneLineBundle` equips exactly this ordinary pulled-back module with
the resulting local trivializations. When `f` is flat,
`familyRankOneLineBundleIso` identifies its image under the original Picard
inclusion with the actual pulled-back coherent family. This is an actual
isomorphism whose underlying module isomorphism is the identity.

Assume also that `f` is locally of finite presentation. Its base-changed
projection has the same property. The actual cartesian rank-one criterion
then proves `familyRankOne_pullback_iff`: for every `h : V ⟶ T`, the ordinary
pulled-back family module is locally free of rank one exactly when `h.left`
has image in `familyRankOneOpen f M`. If `f` is flat,
`familyRankOne_pullback_mem_essImage_iff` expresses the same condition as
membership in the essential image of `PicardGroupoid.relativeToFamily f V`.
All actual module isomorphisms are retained in that essential-image condition.

`familyRankOneLift` uses the open-immersion universal property to give an actual
slice factorization for every such line-bundle pullback. Its factorization
equation follows from the actual open lift, and uniqueness follows from
monicity of the open inclusion. These constructions allow arbitrary,
nonnoetherian, nonreduced, empty and non-quasi-compact tests and require no
flatness of the base-change morphism.

The provenance is the published coherent-family objects and ordinary pullback,
the actual line-bundle inclusion, and the rank-one base-open constructions.
No new external literature assertion is introduced. This pair does not
construct a pseudofunctor transformation, an isomorphism-bearing point-fibre
representation, a coherent-stack atlas, or a Picard-stack atlas.
