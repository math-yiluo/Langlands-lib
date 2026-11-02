# Reindexing distinct related tuples

This derived helper continues the distinct-tuple construction of Stacks Project
Lemma 68.8.3 (Tag 0BBN), used again in Tag 07ST. The registered sources are
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. It constructs the coordinate
permutations and their freeness on nonempty scheme-valued points. It does not
construct their quotient or a stratification. The relation source map is assumed
separated, as in the preceding distinct-locus helper. All schemes have arbitrary
universe `u`, and index `n` means `n + 1` coordinates.

`tupleDistinctOpen_le_preimage` proves that selecting coordinates by an injective
index map preserves distinctness. It uses the inverse-image formula for equality
loci and injectivity of the index map. For a bijection,
`tupleReindex_preimage_distinctOpen` strengthens the inclusion to equality by
writing any pair of indices as images under the bijection.

`tupleDistinctReindex` restricts the tuple reindexing morphism to the distinct
loci. `tupleDistinctReindex_ι` describes its composite with the inclusion, and
`tupleDistinctReindex_projection` gives its coordinates. The coordinate
extensionality lemma `tupleDistinct_hom_ext` follows by cancelling the open
inclusion and using extensionality on the full tuple scheme. Coordinate
extensionality then proves the identity and composition laws
`tupleDistinctReindex_id` and `tupleDistinctReindex_comp`, with the same
contravariant order as reindexing on full tuples.

`tupleDistinctReindexIso` packages the two reindexing maps of an index bijection
and its inverse as an isomorphism. The forward and inverse coordinate equations
are `tupleDistinctReindexIso_hom_projection` and
`tupleDistinctReindexIso_inv_projection`. Its identity, inverse and composition
laws are `tupleDistinctReindexIso_refl`, `tupleDistinctReindexIso_symm` and
`tupleDistinctReindexIso_trans`; they follow by coordinate comparison, with the
inverse law immediate from the definition.

`tupleDistinct_coordinates_injective` states that the coordinate morphisms of
any family over a nonempty scheme are pairwise different. Equality of two
coordinate morphisms would force the entire family into their equality locus;
picking a point of the test scheme contradicts membership in the distinct locus.
`tupleDistinctReindexIso_free` deduces that a permutation fixing such a family
is the identity by comparing every coordinate. This includes geometric points
and uses equality of scheme morphisms, without replacing it by equality of their
ordinary underlying point images. Nonemptiness is essential for this formulation:
on the empty test scheme all coordinate morphisms agree.
