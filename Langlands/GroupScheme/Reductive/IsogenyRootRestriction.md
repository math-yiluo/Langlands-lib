# Actual root restrictions and fppf images

This internal derived module constructs
`RelativeRoot.rootRestrictionOfRootDatumIsogeny`, the actual homomorphism between
arbitrary supplied representatives of corresponding intrinsic split root
subgroups. The base is any field `k : Type u`. The input includes affine ambient
group schemes, a smooth target, supplied split tori and inclusions, finite reduced
root data on their actual character and cocharacter lattices, finite generation
of those lattices, a root-datum isogeny `f`, and actual ambient and torus
homomorphisms satisfying the inclusion square and weight-pullback compatibility.
For a target root index `j'`, the source index is `f.indexEquiv j'`.
The construction uses the published all-test containment
`comp_mem_subgroup_of_rootDatumIsogeny` and the represented-subgroup Yoneda
restriction. The theorem `rootRestrictionOfRootDatumIsogeny_comp` says its
composite with the target representative inclusion equals the source inclusion
followed by the ambient homomorphism.

The theorem `isIsogeny_rootRestrictionOfRootDatumIsogeny` additionally assumes
that both ambient groups are connected reductive, that the split tori are
maximal, that both root data describe the actual ambient roots, and that the
ambient homomorphism is finite. It proves that the constructed restriction is
finite, flat and surjective.

The preceding representative lemmas supply the geometry used in that proof.
Closedness and connectedness transfer from the published canonical root
representatives through their represented-functor isomorphisms; smoothness uses
the published smoothness transfer theorem. Reducedness excludes higher positive
root multiples, using the torsion-free character lattice of the split torus.
The actual represented Lie kernel then identifies with the root weight space,
which is a line by `splitRootLieLine`. Thus
`finrank_lieKernel_eq_one_of_isRepresentedBy_root` computes its Lie finrank as
one. Finiteness of the restriction follows from its inclusion square: the
composite of the closed source inclusion with the finite ambient map is finite,
and the target inclusion is separated. Finally
`isIsogeny_of_isFinite_of_finrank_eq` supplies flatness and surjectivity from
the equal Lie finranks. This argument does not require a separable ambient map,
a smooth kernel, or a perfect base field.

The theorem `isFppfImage_of_rootDatumIsogeny` packages this restriction as an
actual `SubgroupFunctor.IsFppfImage` witness for corresponding roots. Its local
finite presentation follows from finiteness and the locally noetherian smooth
target representative. The converse in `isFppfImage_iff_index_eq` starts with
any source index `j`. All-test containment places that source root in the
prescribed target root with index `f.indexEquiv.symm j`. Fppf-image minimality
and the fppf locality of the represented target root give inclusion of any
claimed target root into this prescribed one. The published reduced root-index
incomparability theorem forces their indices to agree. Consequently the
fppf-image relation holds exactly when `j = f.indexEquiv j'`.

The provenance is an internal composition of the published intrinsic-root
comparison, representability, represented Lie-kernel comparison, split-root
Lie-line and finite-homomorphism results. No independent assertion from external
literature is used as a new premise. This is the root-image part of
`IsogenyRootSubgroupStatement` (proved in `IsogenyRootSubgroupProof`); its
characteristic-power coordinate formula is not part of this module. The universe and field are arbitrary, and the subgroup
comparisons retain every relative test scheme.
