# Connected zero-dimensional smooth groups over a field

Worker 1569.

This internal prerequisite removes the separably closed field assumption from
zero-dimensional triviality in the perfect-field unipotent splitness induction.
It works over every field, without a perfectness or separatedness assumption.

For a connected étale scheme `X` over `Spec k` with a rational section `s`,
`isIso_of_connected_etale_section` proves that the structure map is an
isomorphism. The section is an open immersion because it is a section of an
étale map: the diagonal criterion gives cancellation of an étale map from an
open immersion. It is a closed immersion because a rational point over a field
is closed. Its range is nonempty and clopen, hence all of the connected space
`X`. A surjective open immersion is an isomorphism; the section equation then
shows the structure map is an isomorphism.

`connectedEtaleSectionIso` packages this isomorphism as actual scheme data,
with the original structure map as its forward map.

A smooth group of relative dimension zero is étale. Its unit supplies the
rational section. Consequently its structure map is an isomorphism and its
identity endomorphism equals the constant unit endomorphism.
`eq_zero_of_smoothOfRelativeDimension_zero_over_field` composes this equality
with any group homomorphism to show that the homomorphism is zero.

The construction is derived from Mathlib's étale diagonal and open immersion
criteria. The group-theoretic argument generalizes the Library lemma
`Langlands.GroupScheme.eq_zero_of_smoothOfRelativeDimension_zero`, whose proof
first used the separably closed field to obtain a section. Here the existing
rational identity supplies it directly. This is internal proof infrastructure,
not a separately attributed assertion from the splitness literature.
