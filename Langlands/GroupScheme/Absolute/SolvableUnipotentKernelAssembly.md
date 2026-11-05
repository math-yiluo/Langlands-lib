# Formal assembly of a unipotent kernel

This internal helper module gives the formal kernel step for the proof of
`Langlands.GroupScheme.SolvableUnipotentPartStatement`. It does not establish
Lie–Kolchin, unipotence, smoothness or connectedness of the resulting kernel.

For any homomorphism `q : G ⟶ H` over an arbitrary scheme, its actual
scheme-theoretic kernel is normal on every test scheme by the imported
`HopfPrimitive.isNormal_range_kernelι`. Its proof identifies
kernel points with the points sent to the identity, then applies the group
homomorphism laws to a conjugate. Every homomorphism killed by `q` has its
range subgroup functor in this kernel; this follows directly from the same
pointwise characterization, with no reducedness assumption.

The construction `kernelCompHom j q` is the homomorphism
`kernel (j ≫ q) ⟶ kernel q` induced by `j`. It is defined using the pullback
universal property. Its composite with the second kernel inclusion is the
first kernel inclusion followed by `j`. When `j` is a closed subgroup and
`H` is separated over the base, both kernel inclusions are closed immersions;
the displayed identity and cancellation for closed immersions imply that
`kernelCompHom j q` is also a closed subgroup.

The map `kernelCompTo j q e` composes this construction with the inverse of
any presentation isomorphism `e : U ≅ kernel q`. Closedness is preserved by
the isomorphism. Thus `isUnipotent_kernel_comp_of_closedSubgroup` transfers
unipotence of `U` to `kernel (j ≫ q)` provided that `U` is affine and locally
of finite type over the field. This theorem explicitly assumes the published
proposition `UnipotentClosedSubgroupStatement`; it does not prove that
prerequisite. For a block diagonal projection, the intended presentation is
`GeneralLinear.blockUnipotentIsoKernel`.

Over a field, `IsUnipotent.range_le_kernelι_of_isSplitTorus` applies the existing
`IsUnipotent.hom_eq_zero_of_isSplitTorus` theorem to `w ≫ q`. This holds for
any unipotent source, including nonreduced and disconnected sources, on every
test scheme.

Finally, `exists_unipotent_part_of_split_torus_kernel` assumes that a map to
a split torus has a smooth connected unipotent kernel. It takes that actual
kernel as the required subgroup. A split torus is affine, hence separated,
so its kernel inclusion is closed. Normality and maximality are precisely
the imported normality lemma and the preceding maximality lemma. The closedness premise on each competing unipotent
subgroup is not needed for this formal maximality argument.

The provenance is internal: these statements are consequences of the already
published scheme-theoretic kernel and split-torus annihilation interfaces.
They supply only the formal assembly step and leave the geometric and
unipotence prerequisites explicit.
