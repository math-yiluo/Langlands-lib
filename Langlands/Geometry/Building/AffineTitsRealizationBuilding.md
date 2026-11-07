# Conditional building construction for the actual affine Tits datum

This is an internal deduction from the existing actual quotient, full
Tits-system comparison and face-compatible realization APIs. It introduces no
external source assertion. All field, group and quotient objects remain the
original ones, and the construction works at every universe `u`.

For a general supplied `IsBuildingTitsSystem`, assume explicitly that every
singleton simple type is admissible. `realization_isThick` combines the proved
global chamber-complex result with the proved lower bound of three for the
number of chambers containing a panel. This gives the entire BL1 predicate,
including its polysimplicial, chamber-extension and connectivity clauses.

For each actual apartment, `realization_isThin_apartment` combines its proved
chamber extension and gallery connectivity with the exact count of two
chambers containing each panel. It retains an explicit `IsPolysimplicial`
premise for that apartment. Thus it proves the full BL2 predicate under that
premise. Global polysimpliciality alone is not used to infer the apartment
premise.

`realization_isBuilding` assembles these results with the actual apartment
subcomplex theorem, common-apartment theorem and two-facet apartment
order-isomorphism theorem. The last theorem fixes every subface of either
chosen common facet. Its conclusion is exactly
`AbstractBuilding.IsBuilding R.complex R.apartments`, with all four BL clauses,
under singleton admissibility and the polysimplicial premise for every actual
apartment.

The second part uses the literal affine Tits datum already defined in
`AffineIwahoriTits`: its Weyl group is `P.affinePart`, its projection is
`P.affineTitsProjection`, and its simple set is
`P.chamberSimpleInAffinePart e C`. The multiplicative equivalence `e` to the
geometric affine Weyl group is supplied, as is normality of the original
normalizer-zero subgroup. No identification with an arbitrary simple set is
asserted.

Assume that the original affine roots form an affine root system with rank
zero allowed and that `C` is an actual affine chamber. The proved
`AffineSimpleAdmissibility` result gives a noncommuting chamber-simple neighbor
of `e s`. Pulling it back through `e.symm` gives a simple neighbor of `s`.
Applying `e` to a supposed commutation proves that the two preimages do not
commute. For a singleton type `{s}`, this neighbor supplies an element outside
the singleton in the component of `s`. Every other simple element supplies
itself. This proves singleton admissibility in the actual affine part,
including the vacuous rank-zero case.

`affineTitsRealizationBuilding` consequently constructs the building witness
on the original realization when its full Tits comparison uses precisely that
affine datum. Singleton admissibility is discharged rather than supplied in
this final construction. Its explicit inputs still include the actual
affine-Weyl multiplicative equivalence, the full stabilizer and apartment
comparison, the face-compatible realization, and polysimpliciality of every
actual apartment. The action compatibility of `e` is not needed for this
admissibility transfer and is not asserted here.

This module neither constructs those inputs nor proves the other clauses of
`SatisfiesBuildingAxiom`, namely the polysimplicial group action, torus-apartment
correspondence and normalizer stabilizer. It therefore does not prove the
unconditional `RootValuationBuildingConstructionStatement`.
