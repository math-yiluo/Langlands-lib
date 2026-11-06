# Chambers from the supplied Tits comparison

At arbitrary universe `u`, let `P : ParahoricBuildingData G` be supplied
actual data over a nonarchimedean local field. Retain the full supplied
`hT : P.IsBuildingTitsSystem Ca π Sgen`, a supplied polysimplicial
realization `R` of its existing valuation quotient, and supplied face
compatibility `hR : R.IsFaceCompatible`.

`realization_isChamber_iff_stabilizer` identifies chambers of `R.complex`
with the facets whose stabilizers in the existing group `P.zeroSubgroup`
are conjugates of the distinguished Iwahori
`P.chamberZeroStabilizerIn Ca`. Here chamber means maximal facet under
inclusion, using the existing `AbstractBuilding.IsChamber` predicate.
The original quotient, group action, facets and stabilizer definitions
are retained.

For the sufficient direction, face compatibility and `hT.facetPrecedes_iff`
turn a facet containing the given one into an admissible parabolic
contained in its conjugate Iwahori stabilizer. The internal group lemma
`eq_conjugate_borel_of_isAdmissible_of_le` makes these stabilizers equal.
Injectivity of the supplied stabilizer comparison, followed by injectivity
of `R.realize`, makes the two complex facets equal. This proves maximality.

For any complex facet, its stabilizer is parabolic and therefore contains
a conjugate of the distinguished Iwahori. That conjugate is admissible
by `isAdmissibleParabolic_conjugate_borel`, so surjectivity of the supplied
facet-stabilizer comparison produces an original facet with that exact
stabilizer. Pulling it back through `R.realize` gives a chamber by the
sufficient direction. The same two face comparisons give containment
of the initial complex facet in this chamber. This proves
`realization_exists_chamber_with_stabilizer`. If the initial facet was
already a chamber, maximality makes it equal to the constructed chamber,
proving the necessary direction of the characterization.

`realization_exists_chamber` is exactly the every-facet-in-a-chamber
clause in `AbstractBuilding.IsChamberComplex`. The noncomputable
`realizationContainingChamber` chooses the chamber just constructed;
`realizationContainingChamber_spec` exports its chamber and containment
properties.

All results are internal deductions from the existing
`FullValidity.ChamberAxioms` stabilizer bijection and reverse-inclusion
comparison, the existing `FullValidity.Realization` face comparison, and
the group minimality proof in `TitsBorelChambers`. They introduce no
external mathematical assertion. No geometric building axiom is assumed,
and no apartment-axiom, chart-injectivity, or gallery-connectedness
premise is used beyond the displayed supplied comparisons.

This module does not construct the data, the full Tits comparison, or
the face-compatible polysimplicial realization. It does not prove
gallery connectedness, thickness, apartment thinness, a vertex action,
the complete BL1 or BL2 axioms, or the unconditional
`RootValuationBuildingConstructionStatement`.
