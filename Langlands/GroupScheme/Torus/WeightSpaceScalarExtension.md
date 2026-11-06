# Actual adjoint weight spaces and scalar extension

For an extension of fields `k → K` in arbitrary common universe `u`, an
affine group scheme `G` locally of finite type over `k`, an actual split
torus `T`, and any homomorphism `i : T.toGrp → G`, this module constructs
`weightSpaceBaseChangeEquiv`. Its source is
`K ⊗[k] weightSpace i χ`, and its target is the full actual weight space
for the pulled-back character in the actual base change of `G`.
Reductivity, connectedness, maximality, and injectivity of `i` are not
assumptions. The weight spaces retain their eigenvector equation over
every coefficient algebra.

The construction uses the published complete weight-space comparison
`weightSpace_baseChange_eq_extendedWeightSpace`. The original weight
submodule is first extended into the tensor product of the full Lie
module. Since field extension is flat, Mathlib's
`Submodule.toBaseChange.toLinearEquiv` identifies that extended submodule
with the tensor product of the weight space itself.
The actual Lie equivalence `Lie.schemeScalarExtension` then maps it
injectively into the actual Lie module of the pullback group.
`map_weightSpace_baseChange` identifies its image with the full target
weight space: both are the scalar span of the actual extended original
vectors. Restricting the Lie equivalence and transporting along that
equality yields the declared equivalence.

`weightSpaceBaseChangeEquiv_tmul` states that its value on a pure tensor,
after including the result in the target Lie module, is exactly the
value of the actual Lie scalar-extension equivalence on that tensor.
The equality is definitional for this construction.

`finrank_weightSpace_baseChange` follows from this linear equivalence
and Mathlib's dimension formula for scalar extension.
`weightSpace_line_baseChange_iff` uses the characterization of a
one-dimensional vector space as a space linearly isomorphic to its
field. It preserves and reflects the existence of such a line
trivialization.

Worker 1333 authored this internal derived construction. It reuses the
complete actual weight-space comparison and the scalar-extension
construction, without asserting an additional geometric structure
theorem. The related coordinate construction
`splitTorus.exponentWeightBaseChangeEquiv` works for smooth affine groups
over arbitrary rings and uses a chosen coordinate torus. This module
instead works with a supplied arbitrary split torus over fields, uses
its actual characters directly, and requires only local finite type
of the affine group. The dimension-one root-space theorem remains a
separate obligation: the present result transfers a dimension bound
but does not supply it over an algebraically closed field.
