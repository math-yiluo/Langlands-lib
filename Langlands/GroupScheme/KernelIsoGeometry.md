# Geometry of the kernel of an isomorphism

This internal construction applies to actual group objects `G` and `H` over
an arbitrary scheme `S` and a homomorphism `f : G ⟶ H` with `IsIso f`.
It uses the published scheme-theoretic kernel, without replacing it by a
pointwise kernel.

`kernel_hom_isIso` proves that the actual structure morphism
`(kernel f).X.hom` is an isomorphism. Indeed, the kernel square is the
pullback of `f` along the target's unit section. Pulling back an isomorphism
makes the projection to `S` an isomorphism. `kernelBaseIso f` records this
scheme isomorphism and `kernelBaseIso_hom` identifies its forward map with
the structure morphism.

Consequently, `smooth_isAffineHom_kernel_of_isIso` proves smoothness and
affineness of that morphism over every base. If the base's underlying space
is connected, `connectedSpace_kernel_of_isIso` transfers connectedness
along the induced homeomorphism. There are no finite-type, separatedness,
field or ambient-smoothness hypotheses beyond those already implied by an
isomorphism.

The provenance is internal: the only kernel-specific input is the published
`kernel_isPullback_scheme`; the rest is pullback invariance of isomorphisms,
the geometry of an isomorphism and topological transport along a scheme
isomorphism. This supplies the trivial torus-factor kernel needed by the
parahoric comparison argument; it asserts no geometry for noninvertible
factor maps and no unipotence result.
