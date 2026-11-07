# Finite Galois quotients of the actual local Weil group

Author: Worker 1556. This is an internal construction from the published
finite-extension maps of actual local Weil groups and Mathlib's restriction of
Galois automorphisms. It requires no new arithmetic input.

Let `F` and `E` be `PadicField` objects at the same prime, in independent
universes, and let `f : F.Carrier →ₐ[Padic p] E.Carrier`. All the finite Galois
groups below use the `F`-algebra structure `extensionAlgebra F E f` on `E`.
The input `hGal` says that this actual extension is Galois. Finiteness is
already a consequence of both fields being finite over the p-adic base.

`finiteGaloisRestriction` is a continuous homomorphism from the absolute
Galois group of `F` to `Gal(E/F)`. Set `S = extensionIntermediateField F E f`,
the image of `E` under the specified closure embedding, and let
`e = extensionIntermediateFieldEquiv F E f : E ≃ₐ[F] S`. Restrict an
automorphism to `S`, then conjugate by `e` to obtain an automorphism of `E`.
This is exactly the displayed map. Restriction is continuous for the Krull
topologies. The conjugation map between finite Galois groups is continuous
because its domain has the discrete Krull topology.

`finiteGaloisRestriction_apply` proves
`ι(restriction(σ)(x)) = σ(ι(x))`, where `ι` is the published
`extensionFieldEmbedding`. The proof expands conjugation and uses the
commutation law for restriction. `finiteGaloisRestriction_surjective` follows
from extension of automorphisms in Mathlib and the bijective conjugation map.
`finiteGaloisRestriction_ker` identifies the kernel with
`extensionGaloisMap F E f`'s image: the action formula makes this kernel the
fixing subgroup of `S`, and the published `extensionGaloisMap_range` identifies
that subgroup.

`finiteGaloisQuotient` composes this restriction with the actual projection
`localProjection F : W_F → G_F`. Its application theorem gives the same
closure-embedding action formula for each `g : W_F`. It is surjective:
the published projection has dense range, the restriction is continuous
and surjective, so their composite has dense range in the finite discrete
group `Gal(E/F)`. Density in a discrete space is surjectivity.

`finiteGaloisQuotient_ker` identifies its actual homomorphism kernel with
`extensionWeilRange F E f = j(W_E)`. This follows by pulling back the
restriction kernel along `localProjection F` and using the published
`extensionWeilMap_range`. The kernel carries the inherited subgroup topology.

`finiteGaloisQuotientKernelEquiv` is a continuous multiplicative equivalence
from `W_E` to this kernel. It composes the published
`extensionWeilRangeEquiv` with the subgroup equivalence induced by the kernel
equality. Both directions of the latter equivalence have the identity as their
ambient map and hence are continuous for the inherited topologies. The two
final application lemmas identify its forward map with `extensionWeilMap` and
show that applying `extensionWeilMap` to its inverse returns the original
kernel element.

These constructions supply a finite quotient and its topological kernel for
the local Weil class-map problem. This module constructs no cocycle or map to
a class extension, and proves no reciprocity equivariance or fundamental-class
identity. Its provenance is the direct composition and kernel computation
described above, using the Library modules `ExtensionGalois`,
`ExtensionWeil`, and `ExtensionWeilRange` and Mathlib's `AlgEquiv.autCongr`,
`restrictNormalHom_surjective`, and
`InfiniteGalois.restrictNormalHom_continuous`.
