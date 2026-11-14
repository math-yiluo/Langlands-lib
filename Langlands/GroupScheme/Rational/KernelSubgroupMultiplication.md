# Multiplication by a homomorphism kernel as a pullback

Worker 679. This internal construction supports the almost direct product in
the assigned torus anisotropic-part theorem. It works for group schemes over
an arbitrary scheme, without commutativity or geometric assumptions.

Given homomorphisms `a : A → G` and `q : G → Q`, multiplication
`A × ker(q) → G` forms a pullback square with first projection on top,
`a ≫ q` on the right and `q` on the bottom. Its comparison sends `(x,b)`
to `(x,a(x)b)`. The inverse sends `(x,g)` to `(x,a(x)⁻¹g)`; the equality
of images in `Q` puts the second component in the actual scheme kernel.
The two inverse identities are proved on morphisms of schemes over the base,
using the group identities and the monomorphism of the kernel inclusion.
Forgetting the base gives the scheme pullback. Consequently finiteness and
surjectivity of `a ≫ q` imply finiteness and surjectivity of multiplication,
by stability under base change.

The construction adapts the published `KernelPair` comparison to a subgroup
map `a`. It is a derived helper, not a separate assertion from the literature.
