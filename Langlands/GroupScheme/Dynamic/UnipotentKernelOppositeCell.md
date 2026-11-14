# Opposite dynamic cells under quotients with unipotent kernel

This internal construction specializes the proved binary kernel-cell and
saturation results to actual dynamic subgroups over any field `k : Type u`.
The ambient groups `G` and `Q` are smooth, connected and affine. The
homomorphism `q : G → Q` is smooth and scheme-surjective, and its full
scheme-theoretic kernel is connected and unipotent.

For a cocharacter `χ` of `G`, the factors are any supplied representatives
of `U_G(-χ)`, `P_G(χ)`, `U_Q(-qχ)` and `P_Q(qχ)`. The representation
hypotheses concern the actual subgroup functors on all relative test schemes.
There is no restriction to canonical affine representatives.

`exists_oppositeCellKernelChart` constructs a morphism from the full kernel
of `q` to the product `U_G(-χ) × P_G(χ)` whose composite with ordered
multiplication is the original kernel inclusion. The proof first obtains
smooth, scheme-surjective quotient homomorphisms on both factors using
`exists_unipotentQuotientHom` and `exists_parabolicQuotientHom`. The
represented-structure transport supplies closedness of the four inclusions,
and therefore affineness or separatedness of the required factors.
Smoothness of `q` makes its kernel smooth; its closed inclusion into the
affine ambient group gives affineness and finite type over the field.
The actual source opposite multiplication is open by
`dynamicBaseOppositeCell`, and the target opposite multiplication is monic
by `mono_oppositeCellMul`. The general `KernelCell.kernelChart` theorem
then applies, together with the assumed connectedness and unipotence of the
full kernel. `oppositeCellKernelChart` chooses this chart, and its `_comp`
theorem records the exact ambient composite. This chart is a morphism of
schemes over `k`, with no claim that it preserves a group law.

`oppositeCell_exists_lift_iff` proves, for every relative test scheme `T`,
that `x : T → G` factors through the source opposite cell if and only if
`q x` factors through the quotient opposite cell. It applies the general
`KernelCell.exists_lift_iff` using the preceding chart and the actual
scheme-surjective factor maps. Thus it descends coordinates to the original
test scheme by the source open immersion, without assuming surjectivity on
`k`-points of either factor quotient. `oppositeCellLift` chooses source
coordinates from supplied quotient coordinates, and `oppositeCellLift_comp`
identifies their product with `x`.

The construction is derived from the cited Library declarations and the
proved internal binary-cell lemmas. It supplies the field-group inverse-image
step for the host depth-zero opposite-factor argument. It does not construct
an integral group model, lift a residue normalizer, or prove the host
`UnramifiedFixedDepthZeroOppositeStatement`.
