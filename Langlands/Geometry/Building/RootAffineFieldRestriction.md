# Actual affine root groups under literal field restriction

This internal comparison uses arbitrary fields `k → K` in the same universe,
a smooth affine original group, a monomorphic inclusion of a supplied split
torus, original opposite factor pairs, and a real unit character upstairs
whose restriction is nonzero on some original unit. The upstairs
`KPApartmentData D` is supplied on the literal base changes of the original
group, torus and inclusion. The original apartment is precisely
`fieldRestrict i hS hE ω hω D`.

`fieldExtendAffineFunctional` precomposes an original affine functional with
the proved actual affine restriction equivalence from upstairs to the
original apartment. Its evaluation is the original functional evaluated at
`fieldRestrictPoint`. It equals the existing inverse-precomposition
transport along the inverse restriction equivalence. Positive constant
shifts commute with this construction.

`fieldExtendAffineFunctional_linear` proves that a functional whose
derivative is an original relative-root form extends to a functional whose
derivative is the actual base-changed relative-root form. Every upstairs
translation is the actual base change of an original translation. On those
vectors the inverse linear map cancels base change, and the previously
proved root-form evaluation comparison gives the result.

`affineRootGroup_fieldRestrict` proves exact equality with the subgroup
preimage under actual rational-point scalar extension. This holds for
every nonzero original character and every original affine functional,
without a derivative premise. Expand the root groups as intersections over
their apartment points. The existing exact filtration preimage formula
proves one implication at each restricted point. Surjectivity of the
actual apartment restriction proves the reverse implication at every
original point. Each comparison uses the same real threshold.

`affineRootGroupPlus_fieldRestrict` proves the same exact preimage formula
for the strict root groups. Membership in each strict group has a positive
real constant witnessing membership in the shifted root group. Retain
that constant, apply the root-group preimage theorem, and commute the
constant shift with extension. This proof does not interchange subgroup
preimages with arbitrary generated suprema.

`fieldExtendAffineFunctional_mem_extendedAffineRoots` applies the derivative
comparison to the original relative root. If the upstairs strict and
nonstrict root groups were equal, taking their scalar-extension preimages
and using both proved comparisons would make the original groups equal.
That contradicts the original extended-root condition. Consequently
`transported_extendedAffineRoots_subset` is a genuine inclusion of the
transported original extended-root arrangement into the upstairs one.

`facetRel_extendedAffineRoots_fieldRestrict` follows by evaluating an
upstairs sign relation on each extended original root. Evaluations are
exactly those at the restricted points. Thus the image of an upstairs
extended-root sign facet is contained in the original sign facet through
the restricted point, as stated by
`image_facet_extendedAffineRoots_fieldRestrict_subset`. No apartment axioms
or local-field assumption on the extension field is used.

The provenance is internal: the existing literal apartment restriction,
its bijectivity and exact filtration preimages, actual relative-root base
change and reduced root-form comparison, the definitions of affine root
groups and extended roots, and the existing affine transport and sign
relations. This unit does not assert equality of the complete extended
root arrangements. Ordinary affine roots involve the extra doubled-root
product condition, and their preservation is not proved here. Initial
apartment existence, a larger split torus, Galois fixed-locus geometry,
building axioms, metric construction, and the supplied-model special point
and unique fixation remain separate obligations.
