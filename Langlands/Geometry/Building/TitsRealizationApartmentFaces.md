# Faces and chambers inside apartments from the Tits comparison

This is an internal deduction for supplied actual `ParahoricBuildingData P`,
the full comparison `hT : P.IsBuildingTitsSystem Ca π Sgen`, and, for the
realization results, a supplied `PolysimplicialRealization R` satisfying
`R.IsFaceCompatible`. The field, group, Weyl group and data have the arbitrary
universe parameter `u`. The original quotient, its facets, its rational-point
action and its actual apartments are retained.

The full comparison supplies a saturated Tits system with finite generators,
a bijection from original facets to admissible parabolic stabilizers, reversal
of the face relation to stabilizer inclusion, and the apartment comparison.
All these inputs remain premises. No apartment-axiom witness
`SatisfiesApartmentAxioms`, geometric building witness, or injectivity of the
apartment map is assumed separately.

`subset_apartment_of_facetPrecedes` says that an original subface of a facet
contained in an actual apartment is contained in that same apartment. Choose
a restricted-apartment representative using the supplied apartment
comparison. The larger facet's stabilizer belongs to this restricted
apartment. Face order reversal makes the subface's admissible stabilizer an
overgroup, so `IsTitsSystem.mem_restrictedApartment_of_le` from
`TitsApartmentFaces` puts it in the same restricted apartment. Membership supplies an original facet inside
the apartment with that stabilizer. Injectivity of the stabilizer
correspondence identifies it with the original subface.

`realization_isSubcomplex_apartmentComplex` applies this conclusion through
face compatibility. It proves the exact `AbstractBuilding.IsSubcomplex`
predicate: apartment facets are complex facets, and every complex face of
an apartment facet is again in the apartment.

`realization_exists_apartment_chamber_with_stabilizer` extends a realized
facet lying in an actual apartment to a global chamber lying in that same
apartment. In its restricted apartment, the facet stabilizer contains a
conjugate of the distinguished Iwahori subgroup from the same apartment,
by `IsTitsSystem.exists_conjugate_borel_le_in_restrictedApartment` from
`TitsApartmentFaces`.
The apartment comparison supplies an original facet inside the apartment
with precisely this conjugate stabilizer. Pull it back along `R.realize`.
`TitsRealizationChambers` proves it is a global chamber. The subgroup
containment, reversed by the two face comparisons, proves that it contains
the initial complex facet. The existential also records the conjugating
element of `P.zeroSubgroup` and the exact stabilizer equality.

`realization_exists_apartment_chamber` expresses this as the extension
clause for every member of `R.apartmentComplex Y`, with global maximality
and membership in that apartment. `realizationContainingApartmentChamber`
chooses the proved witness. Its specification retains global maximality,
containment of the initial facet, and containment of its original realized
facet in the supplied apartment.

`realization_isChamber_apartmentComplex_iff` says that a maximal apartment
facet is exactly a global chamber that belongs to the apartment. In the
forward direction, extension within the same apartment and apartment
maximality identify the extended chamber with the initial facet. In the
reverse direction, global maximality restricts to the apartment.

The provenance is the imported definitions and proved subgroup results;
there is no new external assertion. These are conditional consequences of
the supplied full Tits comparison and supplied face-compatible realization.
They do not construct these inputs, prove gallery connectedness, thickness
or thinness, establish BL1 or BL2, construct a vertex action, or complete
the unconditional root-valuation building construction.
