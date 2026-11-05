# Reduction of smooth relative identity components to finite-presentation openness

For an arbitrary smooth actual group scheme over an arbitrary base, an open
immersion whose range contains the entire unit section has product image
containing the relative identity set. On each actual residue fibre, the
pullback image formula and the section-point comparison put the fibre unit
in the pulled-back neighbourhood. `FieldProductCover` places the entire fibre
identity component in its product image. `ProductImage` identifies that image
with the inverse image of the original product image, giving the claimed
containment for every point. If the neighbourhood also lies in the relative
identity set, multiplication closure gives the converse containment.

Assume explicitly the universal proposition
`SectionComponent.FlatFinitePresentationOpennessStatement.{u}`. The global
unit neighbourhood from `UnitNeighbourhood` is then an open subscheme, lies
inside the relative identity set and contains the entire unit section.
`unitProductImage` denotes the range of its actual two-factor multiplication
map. The preceding comparison proves that it equals `underlyingSet`. This
product map is smooth, so its range is open. Consequently the relative
identity set is open.

`smoothExistence_of_isOpen` from `OpenGeometry` constructs the actual smooth open
subgroup representative and proves geometric connectedness of its structure
map. `smoothStructure_of_existence` from `BaseChange` then supplies normality on
every test scheme and compatibility with unrestricted actual base change.
Thus `smoothStructure_of_openness` concludes the exact published
`SmoothStructureStatement.{u}` while retaining the generic openness
proposition as an explicit premise. All universes, bases, smooth groups,
nonreduced tests and base-change morphisms remain unrestricted.

This is an internal derivation from the actual residue-fibre pullback image
formulas, the field product-cover theorem, the global unit neighbourhood,
its smooth multiplication map and the published conditional existence and
base-change results. It does not prove the generic openness premise or the
unconditional parent target. The separate generic openness proof remains
necessary before applying the final reduction without extra premises.
