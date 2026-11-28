# Algebraic torus weights and adjoint Lie weights

For a monomorphism from an affine commutative group to an affine group over a field,
`torusWeightDifferential` evaluates the differential of a character on the
image of the domain's Lie algebra. The injective tangent map identifies that
image with the domain Lie algebra. The scalar is the infinitesimal coefficient
of the character evaluated on the corresponding dual-number tangent point.
Evaluation on a cocharacter tangent recovers the integral character–cocharacter
pairing. Since that pairing separates split torus characters, the
differentiated weights are distinct in characteristic zero.

For an ambient affine group of finite type,
`mem_adjointWeightSpace_of_mem_torusWeightSpace` differentiates the algebraic
weight equation using `adjointDifferentialFamily_targetMap_of_mem_weightSpace`.
The adjoint differential is the bracket by
`adjointDifferentialLieHom_apply_bracket`, so the algebraic weight space lies
in the corresponding simultaneous Lie weight space.

For a split torus, the Lie algebra decomposes as a direct sum of algebraic weight spaces by
`isInternal_weightSpace_of_isSplitTorus`. Projecting a simultaneous Lie weight
vector onto an algebraic summand gives zero whenever the two weight functions
differ. In characteristic zero this shows that each differentiated weight
space is exactly the original algebraic weight space, as stated in
`adjointWeightSpace_eq_torusWeightSpace`. Over any field a nonzero simultaneous
weight space comes from at least one torus character, by
`exists_torusWeightDifferential_of_ne_bot`.
