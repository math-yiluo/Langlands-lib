# Adjoint weights and weight-shifting tangent operators

For a split pinning `p` and an actual representation `r`,
`representationWeightShift p r chi` is the subspace of endomorphisms that
send each actual torus weight space of `mu` into that of `mu + chi`.

An actual Lie element of adjoint weight `chi` gives such an operator.
`tangentMatrix_weight_comm` differentiates the all-algebra adjoint-weight
equation, using the actual conjugation formula for tangent matrices and
compatibility with coefficient extension. It obtains the intertwining
identity between the torus matrix and the extended tangent matrix.
Applying that identity to an actual weight vector proves
`tangentMatrix_mulVec_mem_representationWeightSpace`. Membership in the
target character space is verified on every coefficient algebra; the
universal affine point suffices for the character-space definition.
`toLin_kernelDifferential_mem_representationWeightShift` packages the
result as membership in the defined submodule of endomorphisms.

This is an internal derived helper for the group-side Lie-weight input to
the Weyl character formula for a split reductive group in characteristic
zero. It uses no characteristic-zero, irreducibility, Freudenthal or Weyl
character-formula premise.
