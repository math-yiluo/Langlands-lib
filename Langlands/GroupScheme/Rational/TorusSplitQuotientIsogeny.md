# The largest split part and the invariant quotient

Internal supporting construction for the anisotropic-part theorem.

`IsInvariantQuotient k E q` asserts that pullback of actual characters along
`q` after scalar extension to `E` is injective and has exactly the invariant
integral character lattice of `T` as image.

For a finite Galois splitting extension `E/k`, a largest split subtorus
`a : A → T`, an affine, locally finite type `T`, and a split invariant quotient `q : T → Q`, the implemented
proof shows that `a ≫ q` is finite and surjective. A character of `Q` that
vanishes on `A` has zero Galois trace by the largest-split universal property.
It is invariant, so torsion freeness makes it zero. Conversely, extend a
character of `A` to the split torus over `E` and sum its Galois orbit. The
sum is invariant and hence comes from `Q`. Both `A` and `Q` are split, so
characters descend integrally, giving an element of the pullback image equal
to the Galois-group order times the original character of `A`.

The cokernel is finitely generated and annihilated by that nonzero integer,
so it is finite. Published criteria on actual split torus characters give
finiteness and surjectivity of the underlying scheme morphism. No division
by the Galois-group order or restriction on the field characteristic occurs.

Finally, the actual multiplication morphism `A × ker(q) → T` is a pullback of
`A → Q` by `T → Q`, using `KernelSubgroupMultiplication.isPullback_scheme`.
Finiteness and surjectivity therefore pass to precisely this multiplication
morphism. The kernel's torus and anisotropy properties are proved separately, in `TorusAnisotropicKernel`.
