# Full kernels in compatible product charts

This internal categorical construction supports the kernel argument in
Kaletha–Prasad Proposition 8.4.15. It makes no new assertion from the book:
the full scheme containment and compatible charts are explicit inputs,
and the comparison follows from the published actual kernel pullbacks and
finite categorical products.

Let `q : G → H` be a homomorphism of group schemes over any scheme `S`, and
let `f i : A i → B i` be a finite family of homomorphisms. The source and
target charts `m : product A → G` and `n : product B → H` are morphisms of
schemes over `S`, and both are monomorphisms. They need not be group
homomorphisms. They intertwine `q` with the product of the `f i`, and `n`
takes the distinguished product identity to the identity of `H`.

Assume an actual morphism `l : kernel q → product A` whose composite with
`m` is the full scheme-theoretic kernel inclusion. This is stronger than a
statement only about rational or geometric points; obtaining this morphism
from open-cell geometry remains an obligation for consumers.

`factorKernels` is the actual finite product of the scheme-theoretic kernels
of the `f i`. Its factor inclusions give `inclusion`. Their images in the
target product are all the identity, so composition with `m` factors through
the actual kernel pullback, giving `toKernel`.

Conversely, `l` followed by the product of the `f i` becomes the identity
after the monomorphism `n`, and is therefore already the identity. Each
coordinate of `l` consequently factors through its actual kernel pullback.
Their product gives `fromKernel`. The projection equations and monicity of
`m` and the kernel inclusions prove both inverse equations.

`iso` is an isomorphism of schemes over the unchanged base between
`factorKernels f` and the full ambient kernel. No direct-product group
decomposition is claimed: the source chart can be ordered multiplication of
noncommuting factors. The statement includes the empty index type.
No smoothness, connectedness or unipotence is proved by this construction;
the factor geometry and any transfer through this scheme isomorphism remain
separate obligations.
