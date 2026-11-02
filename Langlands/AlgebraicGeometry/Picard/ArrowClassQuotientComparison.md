# Recognition of the second Picard arrow-class quotient

This is an internal, conditional construction from the published canonical
arrow-class kernel and the generic recognition theorem for etale quotients.
It supplies no geometric quotient theorem.

Let `U` carry an actual line-bundle family `L`. Let `A` represent all its
arrows and let `R` represent the full kernel of the map from arrows to ordered
endpoint pairs. The isomorphism `eA` and pullback square `h` specify these
identifications on every scheme test over the base. All schemes lie in the
arbitrary universe `u`; presheaf values lie in `Type (u + 1)`.

`arrowKernelQuotientSpace` packages the fixed first etale quotient
`arrowKernelQuotientSheaf` as an algebraic space. Its three explicit hypotheses
are that this same underlying presheaf is an fppf sheaf, has representable
diagonal, and admits an etale surjective scheme atlas. None is established
here. The packaging does not change any section type or endpoint map.

The published `arrowKernelQuotient_sectionwise` proves that the two descended
endpoints make this space a monomorphic equivalence relation on `U`, on the
complete section type of every scheme test. `arrowClassQuotientSheaf` is the
fixed etale sheafification of the pointwise quotient by this relation, and
`arrowClassQuotientMap` is its canonical map from `U`.

The further explicit hypothesis `hLocal` is local surjectivity, for the big
etale topology over the base, of the actual map `etaleFamilyMap f L`.
Under this hypothesis, `arrowClassQuotientIso` is a natural isomorphism from
the second quotient to `relativeEtaleClassSheaf f`. The proof specializes
`quotientSheafIsoOfPresentation` to the identity map on `U` and the actual
family map. The quotient presentation is etale locally surjective by the
generic quotient comparison theorem. Its identifications are exactly those
of the family map by `arrowKernelQuotient_relation_iff`. The sheaf target is
the actual etale sheafification of the Picard groupoid's isomorphism classes.
This argument includes sections that have only local arrow representatives;
it does not assert that every arrow-class section has a global representative.

`arrowClassQuotientIso_hom_fac` proves that the recognition isomorphism
preserves the entire presentation map. Composing with the published
`relativeEtaleClassSheafIso` gives `arrowClassQuotientPicardIso`, a natural
isomorphism to the ordinary etale Picard class presheaf.
`arrowClassQuotientPicardIso_hom_fac` identifies the resulting presentation
with the actual etale class of `L`.

Finally, `arrowClassQuotient_picardAtlas` transports a representable diagonal
and a locally finite type etale surjective scheme atlas from the second
quotient to the ordinary Picard class sheaf. These geometric properties are
additional hypotheses. The same source scheme of that atlas is retained.
The module does not prove `SmoothAutomorphismEtaleAtlasStatement`: the first
quotient's geometric hypotheses, etale local surjectivity of the actual
family map, and the second quotient's geometric conclusions must still be
supplied. No unpublished prerequisite is imported or used as an established
result.
