# The closed global intersection quotient and its local comparisons

Worker 1582 constructs the actual presented quotient of the unchanged affinoid
coproduct by the closed contraction ideal from
`SpecialCoverIntersectionKernels`. This is internal derived infrastructure from
actual closed quotients, bounded quotient recognition and full-domain inverse
images. Worker 1685's local special-cover intersections underlie the construction.

`algebra` and `globalMap` are unconditional constructions for two finite
subordinate full-domain covers. The quotient map is admissible with its actual
norm. `Domain.FiniteCover.pullbackWhole` pulls any whole-spectrum finite cover
back to a whole-spectrum finite cover using the actual pushout domains and their
structural maps. `quotientCover` applies this construction to the product cover
and `globalMap`; it introduces no extra algebra for the pulled-back whole domain.

The local comparison is explicitly conditional on the published proposition
`Domain.FiniteCover.IdealEffectivenessStatement`. This file does not prove that
proposition. `localKernel_eq` applies it to the closed exact local kernels and
their already proved overlap compatibility, using specialness of the original
finite chart cover to supply admissibility.

For any bounded base change, `ClosedQuotient.baseChangeEquivOfAdmissibleEpi`
composes the actual closed-quotient base-change equivalence with recognition of
an admissible quotient having the same exact kernel. Its inverse is bounded by
the existing controlled-lift proof. Its entire restriction along the second
pushout leg is exactly the supplied local quotient map.

`localEquiv` specializes this comparison to each product-cover member.
`localEquiv_comp_pullbackMap` and `localEquiv_comp_baseMap` retain the complete
original algebra maps. `localEquiv_comp_leftMap` and
`localEquiv_comp_rightMap` further identify the two original input algebra maps
with the composite actual local-domain inclusion restrictions, using the proved
product-leg identities. Thus these equalities retain nilpotent information and
the original presentations.

Coefficient, ambient-space and original-index universes remain independent.
The construction keeps arbitrary positive radii, trivial valuations, empty
covers and zero or nonreduced algebras. The full special-set intersection result
still needs a proof of ideal effectiveness and the finite geometric recognition
step.
