# Integral prescribed dynamic factors from integral cell coordinates

This internal unit transports actual dynamic representatives through the
generic-fibre identification of an integral model, and identifies prescribed
generic factors with integral cell factors. It retains arbitrary universe `u`.

Let `A` be a domain, `K` a supplied fraction field, and `M` an affine, flat,
finite-type integral model of a group scheme `G` over `K`. Supply an actual
cocharacter `χ` of `M.group`. Its generic cocharacter here means the actual
base change of `χ`, followed by `M.genericIso.hom`.

`isRepresentedBy_generic_unipotent` says that an actual integral representative
of the dynamic unipotent subgroup of `χ` gives a representative of the generic
dynamic unipotent subgroup through `M.genericHom`. The parabolic theorem gives
the same statement for a representative of the dynamic parabolic. The proofs
base change the given representatives and transport them through the supplied
generic isomorphism, using dynamic functoriality under actual isomorphisms.

Assume also that `G` is affine. Supply actual integral representatives of the
opposite dynamic unipotent subgroup and the dynamic parabolic of `χ`.
`integral_dynamic_factors_of_cell_lift` takes integral coordinates of an integral
section `x` in that binary cell, as well as prescribed generic factors `u` and
`v`. The factors must belong respectively to the generic opposite dynamic
unipotent and dynamic parabolic, and satisfy `u * v = M.integralPointMap x`.
The theorem concludes that both prescribed factors lie in the integral-point
subgroup of the original ambient model `M`.

The two generic representative comparisons convert the memberships to actual
generic inclusion ranges. The Library's `Dynamic.mono_oppositeCellMul` proves
monicity of this binary generic cell, without a smoothness assumption.
`ambient_integral_factors_of_cell_lift` then identifies both prescribed factors
with the images of the original integral cell coordinates. No integral models
of the factors and no smoothness, reductivity, Henselian, or residue-field
assumptions are required in this unit.

`integralDynamicFactorLift` selects integral sections mapping to the two
prescribed generic factors, using the two integral-point memberships just proved.
Its subtype records both exact generic images.

The provenance is internal composition of the named base-change,
isomorphism-transport, dynamic monicity, and integral-coordinate comparison
results. This unit assumes integral cell coordinates and does not construct
them or assert the fixed-point opposite-factor theorem.
