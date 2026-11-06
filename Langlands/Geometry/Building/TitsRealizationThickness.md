# Chamber counts from the supplied Tits comparison

At arbitrary universe `u`, retain actual supplied
`P : ParahoricBuildingData G` over a nonarchimedean local field, the full
`hT : P.IsBuildingTitsSystem Ca π Sgen`, a supplied polysimplicial
realization `R` of the existing valuation quotient, and supplied face
compatibility `hR : R.IsFaceCompatible`.

For each complex facet `Fa`,
`realizationChambersContainingEquivBorelsBelow` identifies the actual
chambers containing `Fa` with the conjugates of
`P.chamberZeroStabilizerIn Ca` contained in
`P.facetZeroStabilizer (R.realize Fa)`. The forward map takes a chamber
to the stabilizer of its original quotient facet. The previously proved
chamber characterization makes this stabilizer a Borel conjugate, and
the two supplied face comparisons give its containment in the
stabilizer of `Fa`. The stabilizer comparison and `R.realize` are
injective, so this map is injective.

For surjectivity, a Borel conjugate is an admissible parabolic subgroup.
Surjectivity of the supplied stabilizer comparison therefore gives an
original quotient facet with precisely that stabilizer. Pulling the
facet back through `R.realize` gives a chamber by the existing chamber
characterization. Reverse inclusion of stabilizers and face
compatibility prove that the chamber contains `Fa`. This proves the
equivalence. `realization_encard_chambersContaining` records equality
of the two extended cardinalities, so the correspondence also applies
to infinite sets and counts chambers rather than representatives.

`realization_three_le_encard_chambersContaining_of_ssubset` proves that
any facet which is a proper face of a chamber is contained in at least
three distinct chambers. The chamber stabilizer is a conjugate Borel.
It is contained in the face stabilizer by face compatibility and the
Tits comparison. If the inclusion were reversed, the same comparisons
would imply the reverse face inclusion, contradicting properness.
The existing group theorem giving at least three Borel conjugates
below a strict overgroup, followed by the exact cardinality
correspondence, proves the bound.

`realization_three_le_encard_chambersContaining` specializes this
stronger result to codimension-one facets. Its conclusion is exactly
the chamber-count clause in `AbstractBuilding.IsThick`, used by BL1.

These are internal deductions from `TitsBorelThickness`,
`TitsRealizationChambers`, and the supplied original facet and
stabilizer comparisons. No external mathematical assertion is
introduced. The quotient, action, original facets, and stabilizers
are retained. The module does not construct the supplied data,
Tits comparison, or face-compatible realization. Gallery connectivity,
the full chamber-complex and BL1 properties, apartment thinness,
the remaining building axioms, and the unconditional
`RootValuationBuildingConstructionStatement` remain separate
obligations.
