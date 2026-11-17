# Finite fixed cochains and subgroup descent

This internal adapter connects finite sections of actual ordinary quasi-étale
cochains to the exact three-term descent construction.

The field is complete and ultrametric. The space and chart universes are the
same, as in the quasi-étale site, while the field, group and coefficient
parameters retain the universes used by the global comparison statement. The
group is a topological group. Local smallness and module sheafification of the
ordinary site are explicit assumptions.

`finiteFreeCochainSections` evaluates a cochain using a specified isomorphism of
its source with a finite coproduct of actual free representable sheaves. It
uses the coproduct inclusions, the inverse of that isomorphism and the existing
free-representable section equivalence. For compact representing objects with
supplied action lifts, `finiteCochainFixedSections` applies the proved discreteness
of the equivariant coefficient and the finite fixing-subgroup construction.
The subgroup lies below the prescribed bound and every supplied acting subgroup,
and fixes every section of that cochain.

`OpenSubgroupCochainLift` specializes `EquivariantCochainLift` to the category of
discrete quasi-étale sheaves for a small open subgroup. Its coefficient is the
actual open-subgroup restriction of the original equivariant coefficient. The
published isomorphism commuting ordinary and subgroup restriction supplies
the coefficient comparison. The full-group finite-refinement assumption is
transferred to the open subgroup by
`hasFiniteEquivariantRefinements_compactLiftSystem_subgroup`, giving the
abelian-category structure needed by the model. Twisted module sheafification,
faithfulness and additivity of ordinary restriction are installed from their
proved interfaces. The abbreviation includes no model-existence claim.

For the exactness theorem, the group is small in the coefficient universe and
the full group's compact-lift system has finite equivariant refinements.
No separate subgroup-refinement assumption is needed: the published transfer
theorem supplies it.
`exactAt_of_finiteFixedCochainModels` assumes an exact three-term model with both
differential squares and a lifted cochain whenever its finite sections are
fixed by a common open subgroup. It fixes the sections of each cocycle, obtains
such a model, and uses the published preservation of injective objects under
open-subgroup restriction. The primitive constructed in the model descends to a
primitive in the actual original chain complex. The module-category criterion
then proves exactness of the actual linear Hom complex in the specified
positive degree.

The model-existence hypothesis is a remaining geometric obligation. The finite
presentation alone supplies neither compatible equivariant differentials nor
an equivariant cochain lift. This adapter does not assert unconditional
restricted-injective acyclicity or the global comparison. Its provenance is the
internal composition of the existing finite-fixed-section, subgroup restriction,
free-section and exact-model constructions, with no new literature claim.
