# Characteristic-zero unipotent extensions from vector kernels

This internal construction generalizes the dimension-induction route of the
published `Rational/SplitUnipotentExtensionSection` module by Worker 1459 from torus
quotients to connected reductive quotients in characteristic zero. It is
conditional on two explicit proposition-valued inputs:
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement` and
`CharacteristicZeroReductiveVectorExtensionStatement`. It supplies no proof
of either input and is not the unconditional Levi decomposition theorem.

For a smooth connected affine group `E` and a smooth surjective homomorphism
to a connected reductive `H`, with connected unipotent full kernel, the module
constructs an actual homomorphic section over the original field. First,
`perfectFieldUnipotentSplit` supplies splitness of the full kernel, since a
characteristic-zero field is perfect. The induction uses the smooth relative
dimension of that kernel, not a chosen rational-point dimension.

For a trivial full kernel, faithful flatness, quasi-compactness and
monomorphy show that the quotient is an isomorphism. Otherwise the
stable-vector input chooses a positive-dimensional central vector subgroup
of the kernel, stable for conjugation by the entire extension group. Its
inclusion into `E` is therefore a closed normal subgroup. Quotienting by it
produces a smaller full unipotent kernel. The quotient map to `H` descends by
fpqc homomorphism descent; smoothness and surjectivity descend too. The
induced homomorphism on full kernels is a smooth surjection, so both
unipotence and splitness pass to the smaller kernel. Relative dimensions
add, making the induction strict.

The inductive section is closed because it is a section of a separated
homomorphism. Pulling back the vector quotient along this section gives an
actual affine group scheme with full kernel canonically isomorphic to the
chosen vector subgroup. The vector-extension input supplies a homomorphic
section of this pullback. Composing with its inclusion gives the required
section of the original extension. All kernel comparisons use actual
group-scheme isomorphisms or subgroup-functor equalities on every scheme
test.

`CharacteristicZeroUnipotentExtension.groupSection` chooses the resulting
homomorphism, and `groupSection_comp` proves its composite with the original map
is the identity. No Levi subgroup is assumed. The remaining vector-extension
input is the independent rational-cohomology step; the corresponding
statement companion records its mathematical provenance in Milne 25.48–25.49.
This module is a derived internal assembly of published quotient, descent,
kernel-transport, dimension and perfect-field splitness APIs, with the two
remaining inputs left visible.
