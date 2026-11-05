# Conjugation of arbitrary normalized Jacquet exponents

This internal construction supports the normalized standard-reduction task.
Its provenance is the published general normalized-Jacquet conjugation
construction in `Langlands/Representation/Aubert/General/Conjugation.lean`
and generalized-eigencharacter invariance in
`Langlands/Representation/Filtration/GeneralizedEigencharacterProof.lean`.
It asserts no new source translation.

For closed radical subgroups `N,N'` of a locally compact nonarchimedean
group and normalizing subgroups `L,L'`, suppose one element `g` conjugates
both pairs. If maps from the same group `B` into the two Levi subgroups
correspond under that conjugation, the module map `[v] ↦ [π(g)v]`
is a representation equivalence for the restricted normalized Jacquet
actions. The proof uses the actual coinvariant translation equivalence,
the conjugation identity for the inverse half Haar character, and
the representation multiplication law. No finite-dimensionality,
admissibility or reductive-group hypothesis is used.

The equivalence preserves uniform generalized eigencharacters, by the
published invariance theorem for actual representation equivalences.

For actual represented parabolics, the corollary replaces
`p : P ⟶ G` by `p ≫ (G.innerIso g).hom` and proves equivalence of
`IsNormalizedJacquetExponent` for every character. The supplied maps
`l : M ⟶ P`, `r : U ⟶ P`, and `a : A.toGrp ⟶ M` stay fixed,
as do their Levi, radical, multiplication-isomorphism and split-component
witnesses. Parabolicity of the new map follows from ambient-isomorphism
transport. The actual radical and Levi point images correspond by
`rationalPoints_range_comp_innerIso`, and the split-component point maps
correspond by the rational-point formula for the inner automorphism.
The published equivalence between normalized exponents and generalized
eigencharacters applies using the canonical point topology and the
closedness of the actual Levi images. Field and group universe `u` and
carrier universe `v` remain independent.

This module does not establish existence of standard representatives or
transport root presentations and cones.
