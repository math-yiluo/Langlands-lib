# Actual kernels under an isomorphism of arrows

This is an internal categorical construction from the published pullback
kernel, its universal property, and invariance of smoothness, connectedness
and representation-theoretic unipotence under isomorphism. It has no new
literature theorem as an input or output.

`kernelSquareIso` takes group schemes over the same base, maps `q : G → H`
and `q' : G' → H'`, isomorphisms `e : G ≅ G'` and `d : H ≅ H'`, and the
commutative-square equation `e.hom ≫ q' = q ≫ d.hom`. It constructs an
isomorphism of the actual scheme-theoretic kernels, using maps of the two
pullbacks along their units. Group homomorphisms preserve the unit, so the
second pullback compatibility equation is automatic. The inverse uses the
inverse source and target isomorphisms. Pullback uniqueness proves the two
inverse identities. `kernelSquareIso_hom_ι` gives the compatibility with the
kernel inclusions.

`smooth_connected_of_groupIso` transfers smoothness and connectedness over
any fixed scheme base. Smoothness follows by composing the target structure
map with the scheme isomorphism; connectedness follows from its induced
homeomorphism. Over any field, `smooth_connected_unipotent_of_groupIso`
also transfers `IsUnipotent`, using the published transport of coefficient
representations.

The construction compares actual kernels, rather than only their rational
points. It supplies a presentation-change step for integral-model kernel
arguments; it asserts no kernel geometry without the corresponding geometry
of the comparison kernel.
