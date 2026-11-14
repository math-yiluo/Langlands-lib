# Borel families and their parameter images

This module derives the bridge between the Borel locus of an actual relative
parabolic family and restrictions of that family to test schemes. It uses the
existing Borel-locus base-change theorem and the actual ambient comparison in
`TorusSubgroupModuli.familyHom`. It does not construct a parameter scheme or
assume that the original family is universal.

`RelativeLevi.borelLocus_comp_iso` proves that changing the ambient group by an
isomorphism leaves the Borel locus unchanged. The proof applies the published
geometric Borel ambient-isomorphism equivalence after pullback to each residue
field. Combining this with Borel-locus base change proves
`TorusSubgroupModuli.borelLocus_familyHom`: the Borel locus of an evaluated
family is the inverse image of the original locus under its parameter
morphism. Reductivity of the original ambient group and relative parabolicity
of the original family are explicit premises of this base-change assertion.

`mono_familyHom` proves monicity of the evaluated inclusion from monicity of
the original inclusion. It uses monicity of pullbacks and of the actual
ambient pullback-comparison isomorphism.
`isRelativeBorelSubgroup_familyHom_of_evaluate_eq` combines this fact with
relative Borel invariance under equality of monic all-test ranges.

`isRelativeBorelSubgroup_familyHom_iff` says that evaluation of a relative
parabolic family is a relative Borel subgroup exactly when the image of the
parameter morphism lies in the original Borel locus. The forward implication
uses the evaluated family's geometric Borel residue fibres and the inverse-image
identity. For the converse, that identity supplies all geometric Borel residue
fibres. Their parabolic properties, pullback stability of smoothness and
affineness of the source, and the proved monicity construct the complete
relative Borel predicate.

Finally, `range_subset_borelLocus_of_evaluate_eq` applies these results to a
parameter whose evaluation has the same all-test subgroup functor as a
supplied relative Borel subgroup. Its image therefore lies in the Borel locus.
All equalities of subgroup functors in these results concern every test
scheme.

`relativeBorelFamilyAt` packages evaluation at a parameter whose image lies in
the Borel locus. It returns the actual pulled-back source and inclusion, with
the proved relative Borel property. `relativeBorelFamilyAt_val` records that its
inclusion is definitionally `familyHom j a`.
