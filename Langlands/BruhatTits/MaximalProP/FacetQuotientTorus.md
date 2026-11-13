# Chamber quotients on supplied KP data

For a nonarchimedean local field `F : Type u`, an affine group scheme `G`,
and a supplied `KPBuildingDatum G` satisfying `SatisfiesGroupAxioms`,
`facetQuotient_isTorus_iff_isChamber` proves that the actual reductive
quotient of any building facet is a torus if and only if that facet is a
chamber. The universe `u` is arbitrary. There is no extra facet-comparison
or finite-field theorem premise.

`chamberQuotientCommGroupScheme` uses this equivalence to equip the
supplied quotient of a chamber with its commutative group structure.
Its underlying group scheme is definitionally the supplied quotient;
the constructor does not replace the quotient or its projection.

The generic helper proves that a quasi-split connected reductive group
with empty root support for a maximal split torus is a torus. A closed
torus represents one maximal split torus's centralizer. Rational
conjugacy transports that representative to the supplied maximal split
torus. Empty roots imply centrality, making its centralizer the whole
group, so the representative is isomorphic to the group.

The geometric helper identifies empty facet derivative roots with the
chamber condition by the facet sign relation and the equality of the
affine derivative roots with the actual relative root forms.

For the actual quotient, choose a translated apartment presentation of
the facet. Apply the supplied common-torus clause to the facet paired
with itself. Generic rigidity identifies its neutral model endomorphism
with the identity, and hence also identifies the special-fibre map with
the identity. The resulting maximal split torus inclusion is therefore
the direct inclusion used by the supplied derivative-root-datum clause.
Equality of the paired root-coroot graphs identifies emptiness of the
quotient roots with emptiness of the facet derivative roots.

The quotient is connected reductive by the supplied quotient axiom,
and quasi-split by the published finite-field quasi-splitness theorem.
Empty roots therefore imply that it is a torus by the generic helper.
Conversely, a torus is commutative, so the published commutative-group
root-vanishing theorem gives empty roots. Finally, the published
translated-chart chamber equivalence transports the geometric helper
back to the original building facet.

This is an internal composition of the existing finite-field,
centralizer, generic-rigidity and KP validity interfaces. The imported
`FacetReductiveComparisonStatement` is used only for the existing data
and names; its proposition is not assumed. This unit proves the first
clause of `FacetReductiveComparisons`. It does not prove its Borel-image
or radical-preimage clauses, or the full maximal pro-p proposition.
