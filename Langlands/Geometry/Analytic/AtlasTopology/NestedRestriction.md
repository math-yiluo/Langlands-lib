# Nested subspace restriction of quasinet families

This internal topological construction identifies nested restrictions of
contained-member families. It is used to compare domains and coverings for an
original-chart subspace atlas with those of its ambient atlas.

## Source context and provenance

The quasinet convention is Vladimir G. Berkovich, *Etale cohomology for
non-Archimedean analytic spaces*, Publications mathematiques de l'IHES 78 (1993),
section 1.1, printed page 13 / PDF page 10. The source uses the induced topology
on subspaces and finite families whose members all contain the point and whose
union is a neighborhood. The analytic-domain and covering context is section
1.3, printed pages 23 and 25 / PDF pages 20 and 22. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The present lemmas are derived consequences of the published definitions
`restrictedFamily` and `IsQuasinet` and the existing homeomorphism-transport
theorem. They are not additional assumptions on a family. The ambient space is
an arbitrary topological space; no compactness, separation, or net hypothesis
is required.

## Construction and proofs

For actual subsets `T ⊆ S`, `nestedRestrictionHomeomorph` identifies the subtype
`T` of the ambient space with the subtype `Subtype.val ⁻¹' T` of `S`. Both maps
insert or forget the intermediate membership proof; continuity follows from
subtype continuity.

`nestedRestrictionHomeomorph_imageFamily` proves equality of the transported
family and the family restricted first to `S` and then to `T`. An original
member contained in `T` is contained in `S`. Conversely, containment in the
copy of `T` inside `S` recovers its ambient containment in `T`. These facts
identify each member of the two families.

The two quasinet equivalences apply the published invariance under a
homeomorphism. `isQuasinet_restrictedFamily_subtype_iff` handles an arbitrary
subset `U` of `S` by taking its actual ambient image, whose preimage is exactly
`U` because the subtype inclusion is injective.

`restrictedFamily_subtype_images` proves that taking ambient images of an
arbitrary family on `S` and then restricting back recovers that family.
`isQuasinet_restrictedFamily_subtype_images_iff` combines this identity with the
preceding equivalence. It compares the full finite-neighborhood quasinet
condition on corresponding target subsets, including empty subsets and empty
families.
