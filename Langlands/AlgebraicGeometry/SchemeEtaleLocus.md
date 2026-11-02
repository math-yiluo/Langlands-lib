# The etale locus of a scheme morphism

This internal construction defines `schemeEtaleLocus f` for a scheme morphism
`f` locally of finite presentation. Its points are exactly those where the map
on local rings is formally etale. The construction and proofs adapt Mathlib's
scheme smooth-locus argument to Mathlib's ring etale locus; they impose no
Noetherian or field hypothesis.

`formallyEtale_respectsIso` derives invariance under arrow isomorphisms from
the corresponding facts for formal smoothness and formal unramifiedness.
`formallyEtale_stalkMap_iff` identifies the stalk condition with formal
etaleness of the localization of an affine chart at its corresponding prime.
The arrow identification is Mathlib's `IsAffineOpen.arrowStalkMapIso`;
formal etaleness is unchanged by localization of the base at the image prime.

`exists_etale_of_formallyEtale_stalk` uses finite presentation and the ring
etale-locus theorem to choose a principal open affine neighborhood on which
the coordinate-ring map is etale. Every point of that neighborhood has a
formally etale stalk, proving openness of the set used in the definition.

The remaining lemmas show that the locus is the whole source exactly when
`f` is etale, and that it pulls back along open immersions. Consequently,
`etale_schemeEtaleLocus` proves that its inclusion followed by `f` is etale.
`exists_open_etale_of_formallyEtale_stalk` supplies this neighborhood for any
point satisfying the stalk condition. These results provide neighborhoods;
they do not assert the existence of transverse slices or good points.
