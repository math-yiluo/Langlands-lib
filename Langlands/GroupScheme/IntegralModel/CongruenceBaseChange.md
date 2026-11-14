# Congruence kernels under local coefficient extension

This is derived infrastructure for the reduction-preimage assertion. It uses
the existing integral models, their actual pullback base changes, and the local
residue-field map. It introduces no claim from an external source.

For a local homomorphism of local domains `R → A` and a compatible fraction-field
extension `K → L`, `congruenceKernelBaseChange` restricts the usual extension of
integral sections to the congruence kernels. The proof uses
`ResidueField.map_comp_residue` to commute the residue square. A section whose
restriction to the original residue field equals the identity therefore has
identity restriction after extension. Equality of the actual pullback sections
is checked on both pullback projections.

`rationalExtend_mem_baseChange_congruenceSubgroup` transports this containment
through the given generic-fibre identifications, using
`baseChange_integralPointMap` and the published equality of `rationalExtend`
with `baseChangeSectionHom`.

`congruenceSubgroup_le_integralPoints_of_baseChange` assumes an upstairs
congruence containment and that `A` meets `K` in `R`, inside `L`. It extends a
downstairs congruence point, applies upstairs containment, then reflects
integrality by `mem_integralPoints_rationalExtend_iff`.
`congruenceSubgroup_le_integralPoints_of_unramified` specializes this argument
to the actual integers in the inertia fixed field of a nonarchimedean local
field, using `unramifiedIntegerRange_intersection`.

Smoothness, Henselianity and facet data are not hypotheses of the generic
results. The unramified specialization uses the local-field typeclasses. No
upstairs congruence containment or parabolicity is proved here.
