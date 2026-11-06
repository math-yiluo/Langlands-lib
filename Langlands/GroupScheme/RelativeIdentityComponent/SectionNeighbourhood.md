# Sections near the relative identity component

This internal construction uses the published smooth relative identity-component
structure theorem to restrict an actual section near a point where it lies in the
identity component. It retains arbitrary base schemes, including nonreduced and
nonnoetherian bases, and allows disconnected ambient fibres.

For a smooth group scheme `G/S` and a section `g : S → G`, the open subset
`sectionIdentityOpen G g` is the inverse image under `g` of the relative identity
set. The theorem `mem_sectionIdentityOpen_iff` identifies its membership with
membership of the actual residue-fibre point selected by `g` in the connected
component of the actual fibre identity point.

Given a point `s` satisfying that criterion, `sectionIdentityNeighbourhood`
constructs `SectionIdentityNeighbourhoodData`. It contains an actual open
neighbourhood of `s`, a geometrically connected group scheme representing the
relative identity component, its actual inclusion in `G`, and a morphism lifting
the restricted section. The `recovers` field is an equality of scheme morphisms:
the lifted section followed by inclusion equals the original section restricted
to this open. The only group hypothesis for this neighbourhood construction is
smoothness. The subgroup and its properties are obtained from `smoothStructure`.
The existence proof uses `sectionIdentityOpen`; the exported choice guarantees
the fields of the data structure and does not specify equality with that
particular open.

The field comparisons retain the actual field-valued map `q : Spec K → S`.
`fieldSection` is the rational point of the actual group pullback along `q`
induced by the given section. If the range of `q` is contained in the constructed
open, `fieldLift` lifts it to the actual pullback of the representing subgroup.
`fieldLift_comp` proves that its image is the same rational point, as an equality
in the category of schemes over `Spec K`. Geometric connectedness of the
representing subgroup implies connectedness of this field pullback. Its
inclusion therefore has image in the actual fibre identity component.
`range_fieldSection_subset_identitySet` makes this conclusion without an
affineness hypothesis on the ambient group.

When `G/S` is affine, `fieldIdentityPoint` is an actual rational point of the
existing group scheme `identityComponent ((baseChange q).obj G)`. It is obtained
by factoring the same `fieldSection` through the open identity-component
inclusion. Its inclusion recovers `fieldSection`; `fieldIdentityPoint_recovers`
then proves that inclusion followed by the actual pullback projection equals
`q ≫ g`.

For each point `t` of the open, `geometricIdentityPoint` specializes this
construction to the Library's exact `geometricPoint S t`, using the chosen
algebraic closure of the actual residue field. Its target is precisely
`identityComponent (geometricFiber G t)` over that algebraic closure.
`geometricIdentityPoint_recovers` states the same original-section recovery
equation for this actual geometric fibre. No replacement fibre or unspecified
field is used.

The implemented proof first obtains openness from the open subgroup supplied by
`smoothStructure` from the module `RelativeIdentityComponent.SmoothProof`: its image is
`underlyingSet G` by `IsRelativeIdentityComponent.range_eq_underlyingSet`.
Taking its inverse image gives the required base open. The all-test
factorization criterion constructs the section lift. For every field-valued
point in this open, the actual pullback point equivalence from
`AbelianScheme.KernelBaseChange` transports that lift and its recovery equation.
Connectedness and preservation of the group identity put its image in the
field identity component. Finally `FiniteEtaleImage.liftOver` factors through
the actual open identity-component inclusion. The geometric specialization
uses the defining residue-field factorization of `geometricPoint`.

All declarations are uniform in the arbitrary universe `u`. This is an internal
composition of published constructions; it introduces no additional literature
assertion. The smooth relative structure theorem's SGA 3 and EGA provenance is
recorded in its own companions. The present construction provides the
identity-component restriction needed for a locally extended transporter or
normalizer section. It supplies neither Weyl elements nor maximality,
centralizer criteria or the final openness of the reductive locus.
