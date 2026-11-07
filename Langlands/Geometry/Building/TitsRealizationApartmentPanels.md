# Exact chamber counts over panels of actual apartments

The inputs are actual `P : ParahoricBuildingData G` over a nonarchimedean
local field, the full supplied comparison
`hT : P.IsBuildingTitsSystem Ca π Sgen`, a supplied polysimplicial
realization `R` of the existing valuation quotient, and
`hR : R.IsFaceCompatible`. Every result retains these inputs at arbitrary
universe `u`.

`realization_isCodimOneFace_of_apartment` transfers codimension one from
an actual apartment to the full complex. Every intermediate global
facet lies in the apartment because it is a face of the containing
apartment chamber; the imported subcomplex result supplies this fact.
`realization_stabilizer_eq_of_isCodimOneFace` turns such a global
codimension-one face into a cover among admissible parabolics. The
supplied stabilizer surjection realizes any intermediate admissible
parabolic by a facet. The reverse face comparison places it between the
two given facets, so codimension one forces it to be the smaller facet.

For an actual apartment `Y` and a representative `a` identifying its
facet-stabilizer set with the restricted apartment,
`realizationApartmentChambersContainingEquivBorelsBelow` maps a chamber
containing a facet to its original stabilizer. The imported equivalence
between global and apartment chambers supplies the Borel condition,
and face compatibility supplies the containment. The stabilizer
bijection and the realization equivalence prove injectivity. For
surjectivity, membership in the restricted apartment gives an original
facet contained in `Y` with exactly the specified stabilizer. The Borel
condition makes it an apartment chamber, and the subgroup inclusion
makes it contain the supplied facet. This gives equality of extended
cardinalities without a finiteness hypothesis.

For a codimension-one face of an apartment chamber, that chamber's
Borel stabilizer has a normalizer representative in the apartment.
Its stabilizer is properly contained in the panel's stabilizer.
The cover result and `TitsApartmentPanels` give exactly two apartment
Borels below the latter. Right-normalizer invariance returns to the
original apartment representative, and the equivalence transfers
the count to actual apartment chambers.

`realization_encard_apartment_chambersContaining_eq_two` states the
result for every codimension-one facet of each supplied actual
apartment. This is precisely the count conjunct of
`AbstractBuilding.IsThin` used in BL2. The polysimplicial and gallery
clauses of a chamber complex, full thinness and BL2, existence of the
supplied data and comparisons, and the unconditional root-valuation
building construction remain separate obligations.

This module is an internal deduction from `TitsApartmentPanels`,
`TitsRealizationApartmentFaces`, and the supplied realization and
stabilizer comparisons. It introduces no external assertion and
preserves the existing valuation quotient, apartment subsets, original
facet stabilizers, and rational-point action.
