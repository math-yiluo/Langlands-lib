# A single section level from finitely many compact-picture vectors

`exists_span_le_orbitSectionFixedCoefficients` places the span of any finite
family of compact-picture vectors inside the fixed coefficients of one
`H × H` with `H` open and contained in `K`. Each vector has an open stabilizer
in the compact product representation. Intersect the stabilizers, map to
the full product group and intersect the two factor preimages with `K`.
Linearity makes the entire span fixed by this common product subgroup.

`orbitSectionLevelOfFixedRestriction` takes an actual smooth orbit section
whose compact restriction is fixed by `H × H` at each parameter. Equivariance
and faithfulness of compact restriction show that the whole section is fixed
by that subgroup. The construction views the original section at level `H`,
and inclusion at the full section space recovers that section.

These are derived fixed-level steps for the weak constant term. They allow
an entire family of sections whose coefficients lie in the same finite span
to use one lower level in the derivative estimate.
