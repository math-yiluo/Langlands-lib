# Unramified descent of group-valid Bruhat–Tits data

`unramifiedDescentOfGroupAxioms` proves
`UnramifiedDescentOfGroupAxiomsStatement` in universe `u`. The replacement
uses the supplied parahoric building, polysimplicial realization and
apartment splitting. The equivalence of reduced buildings uses the
identity map and the reflexive building isomorphism in both directions.

`specialTorusExistence` supplies a special torus containing the reference
maximal split torus. `UnramifiedBuildingDescent.exists_omegaCompatible`
chooses a compatible upper valuation class, and
`MaximalUnramified.galoisStable_of_isOmegaCompatible` gives its coefficient
stability. The reference apartment descent uses the same `buildingData`
and `semilinearData` as the predicate. It identifies the image of the
injective, equivariant building map with the fixed locus. The special
apartment comparison gives the exact fixed range and cocharacter linear
part in every chart. It uses `unramifiedAffineRootRestriction` in the set
form of UR 3.

`BuildingModelFamily.exists_satisfiesModelAxioms_withBaseChange_of_unramified`
constructs the replacement models from the image of each indexed subset
under this embedding, using `unramifiedParahoricModel`,
`unramifiedSmoothModelDescent` and `unramifiedZeroDescent`. It gives the
full and neutral integral-point identities over the unramified integers
and the lower model axioms. The upper models in UR 4 are the base changes
of this family, with their relative components. The two model
isomorphisms are reflexive and induce the identity on the generic fibre. Comap of integral points under scalar extension,
combined with the lower integral-point axioms, gives the two fixer
intersection identities.

`BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified` uses the
neutral point identities to construct the new reductive quotient family
and its root reflection data. The inputs are the model kernel, common
torus, parabolic order, root datum and positive radical results, and the
parabolic image deduced by
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel`.
The group axioms for the retained building are those of the supplied datum.

The source is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*
(`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`),
Axiom 4.1.27, §§9.2.1–9.2.5, Propositions 9.3.13 and 9.4.28, and §9.5.
See the authors' *Corrections and additions* of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`),
PDF pp. 27, 37 and 39 for the axiom list, connected-model point identity
and fixed-point arguments.
