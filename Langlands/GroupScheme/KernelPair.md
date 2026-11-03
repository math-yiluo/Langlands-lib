# The kernel trivializes the kernel pair

This derived construction concerns an arbitrary group-scheme homomorphism
`q : G ⟶ Q` over an arbitrary scheme `S`. It uses the existing represented
kernel and the actual fiber product in `Over S`.

The morphism `KernelPair.action q` takes `(g,k)` to `g i(k)`, where `i` is the
kernel inclusion. The kernel equation implies that this point and `g` have
the same image in `Q`. Thus `KernelPair.hom q` is a morphism to
`G ×[Q] G`. Its inverse, `KernelPair.inv q`, sends `(a,b)` to
`(a,a⁻¹b)`; the difference factors through the actual kernel by its published
pullback universal property.

The two compositions are identities by the noncommutative group identities
`g⁻¹(gk)=k` and `a(a⁻¹b)=b`. Product and pullback extensionality prove these
identities as morphisms. `KernelPair.iso q` packages the resulting isomorphism
of actual schemes over `S`. The projection formulas are stated explicitly.
No flatness, surjectivity, smoothness, field, or commutativity hypothesis is used.

`KernelPair.isPullback q` is the kernel action square in `Over S`.
Applying the pullback-preserving forgetful functor gives
`KernelPair.isPullback_scheme q`. The associated `KernelPair.schemeIso q`
identifies the underlying scheme of `G ×[S] ker(q)` with the scheme fiber
product `G ×[Q] G`; its two projection formulas are also explicit.

The provenance is internal: the construction follows directly from
`kernel_isPullback`, `kernelι_mono`, the point-group laws of actual group
objects, and the product and pullback universal properties in Mathlib.
It is infrastructure for quotient and preimage geometry, and asserts no
quotient-existence, affineness, or unipotence result.
