# Actual restricted tensor products of scalar lines

This internal construction evaluates the existing algebraic restricted tensor
product of scalar lines by multiplication. The coefficient field, index type
and family of groups have independent universes. No topology on the field,
groups or representation carriers is required. The finite exceptional set is
arbitrary, including empty; every reference vector is scalar one.

`scalarStageEquiv` is the linear equivalence underlying Mathlib's
`PiTensorProduct.constantBaseRingEquiv`. On an elementary finite tensor it is
the product of its entries, including the empty product. The transition map
adjoins entries equal to one. `scalarStageEquiv_transition` proves that these
finite products are compatible: after expressing products over finite subtype
indices as finite-set products, the additional entries contribute one.

`scalarEvaluation` descends this compatible family through the existing actual
direct limit. It evaluates every elementary restricted tensor by the product
of its finite entries. The map is injective because every difference comes
from a finite stage and evaluation at that stage is an equivalence. It is
surjective because the inverse stage equivalence at the exceptional set
represents every scalar. `scalarEquiv` is the resulting genuine linear
equivalence from the constructed direct limit to the coefficient field.

For a family of groups with specified reference subgroups,
`trivialScalarTensorEquiv` identifies the existing restricted tensor
representation of the trivial scalar actions with the trivial global action.
The local actions are identity maps, so the published identity law for maps of
restricted tensor products proves equivariance.

For a supplied global unit-valued character `χ`, an explicit hypothesis says
that `χ` is trivial on the entire reference tail for the chosen finite set.
This includes elements with infinitely many nonidentity integral coordinates.
The published singleton restriction defines each `localCharacter`.
`characterScalarReference_fixed` proves that its scalar representation fixes
one outside the exceptional set.
`characterScalarTensorEquiv` constructs an actual equivalence from the
restricted tensor of these local scalar-character representations onto the
global scalar-character representation. It composes the published comparison
between tensoring local twists and the global twist with the twist of the
trivial scalar tensor equivalence. Its elementary-tensor formula is again
the product of the entries.

The construction reuses the published restricted tensor direct limit, maps,
genuine restricted-product action, full-tail character formula and scalar-twist
comparison, together with Mathlib's finite scalar tensor equivalence.
It introduces no original-literature identification. Full-tail triviality is
an explicit input here; no existence of a tail for an arbitrary character,
topological tensor completion, general representation factorization or
automorphic occurrence is asserted.
