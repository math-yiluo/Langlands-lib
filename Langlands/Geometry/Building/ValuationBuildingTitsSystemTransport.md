# Tits-system comparison on actual valuation quotients

This derived unit transports all six clauses of `IsBuildingTitsSystem`,
then `HasTitsSystem` for every target chamber, on two supplied actual
parahoric-building data over the same field and group at arbitrary universe
`u`. The group of rational points and its action are the existing ones.

The inputs retain equality of the supplied zero subgroups, an embedded-torus
isomorphism, an equivariant equivalence of the actual reduced quotients that
preserves facets and apartments, an affine apartment equivalence compatible
with the quotient maps, and equality of the full transported affine-root
sets. The zero-subgroup equality is essential: this datum depends on supplied
derived-group data and is not silently treated as canonical.

`normalizerInZero_map_of_torusIso` identifies the full normalizers inside
the supplied zero subgroups. `titsProjectionOfComparison` precomposes the
source projection with the inverse of their multiplicative equivalence. Generic `TitsSystemEquiv` transports the Weyl projection,
Tits axioms, saturation and all admissible parabolic types; finiteness
of the unchanged generating set is copied from the source witness. Equivariance compares the stabilizer of every full subset, giving
the chamber and facet stabilizer identities. The facet equivalence then
transports the bijection onto all admissible subgroups. The existing full
face comparison and reflection of subgroup inclusion transport the face
relation. Finally, the image of every translated apartment contains exactly
the corresponding full set of facet stabilizers, and the full set of these
apartments agrees with the transported restricted apartments.

Every target chamber is pulled back by the inverse affine equivalence.
The source Weyl group is retained in `Type u`, together with the same finite
generating set, without a rank restriction. The provenance is internal derivation from the
unchanged predicates and existing quotient, face, subgroup and Tits-system
transport definitions. Both actual data, all comparison inputs and the
source Tits-system witness remain premises. No unconditional construction
or five-axiom existence theorem is asserted.
