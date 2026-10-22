# Fixed-field units and quotient cohomology

This internal interface identifies the actual invariant submodule of
`unitsRepresentation K L` with the additive notation for the units of
`IntermediateField.fixedField H`. The fields have independent universes.
The subgroup need not be finite or normal for the coefficient equivalence.

The forward map takes a fixed unit to the unit of the fixed field with
the same value. Its nonzero certificate comes from the original unit.
The inverse is the actual inclusion of units from the fixed field into
the ambient field. Extensionality on units and subtypes proves the inverse
identities and additivity. Compatibility with integer multiples proves
linearity for `IntegerScalars`, since the action of a lifted integer is
the integer action of its value under `ULift.down`.

For a Galois extension and a closed normal subgroup, Mathlib's
`InfiniteGalois.normalAutEquivQuotient` identifies the quotient Galois
group with the Galois group of the fixed field. Equivariance is proved
on quotient representatives using `AlgEquiv.restrictNormal_commutes`.
`fixedFieldCohomologyIso` is then `groupCohomology.mapIso` for these
explicit group and coefficient equivalences, in every natural degree.

The provenance is internal: the module connects the project's existing
coefficient and cohomology definitions to Mathlib's fixed-field and
infinite Galois correspondence APIs. It introduces no alternate cohomology
model and assumes no vanishing or local class formation. It does not assert
finite dimensionality of an arbitrary closed subgroup's fixed field,
continuous comparison invertibility, or inflation injectivity.
