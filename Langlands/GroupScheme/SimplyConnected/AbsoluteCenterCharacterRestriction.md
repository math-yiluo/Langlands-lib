# Kernel of restriction to the actual full centre

Author: Worker 177.

Let `d : TitsIndexData G` for an affine, locally finite type group scheme `G`
over a field `K`. The datum supplies semisimplicity, a ground-field maximal
torus, and its split pinning over `SeparableClosure K`. The map
`d.centerCharacterRestriction` is integral character precomposition along
the actual centre inclusion into the absolute torus. It uses `d.toralCenter`,
whose base change is the full scheme-theoretic centre. The construction
and kernel theorem apply in every field characteristic and universe.

`ker_centerCharacterRestriction` identifies its kernel with the full
integral root span. Every root restricts trivially by the published centre
character calculation, so its integral span lies in the kernel.

For the reverse inclusion, semisimplicity over the separable closure gives
finite index of the integral root lattice. Realize the adjoint root datum
whose character lattice is that root lattice. The split central isogeny
theorem realizes the inclusion of character lattices by a homomorphism
of split maximal tori inside an actual central isogeny. In the proof the
character pullback has precisely the integral root span as its image.

The published kernel comparison places the annihilator of this image in
the ambient central isogeny's kernel. On every test scheme its torus
points therefore map into the full centre. They lift to the chosen centre
representative, and cancellation through the closed torus inclusion
identifies their original torus points with those lifts. Any character that
restricts trivially to the centre evaluates to one on these points.

For a split torus with character lattice `X` and an integral submodule `N`,
the identity point of the diagonalizable group of `X / N` gives a universal
character of `X / N`. Precomposing with the quotient map gives a torus
point in the annihilator of `N`. Its value on a character detects the
character's quotient class, since evaluation at this identity point is
injective by the group algebra monomial calculation. Apply this to the
pullback image of the split torus map to obtain the reverse inclusion.
The test scheme retains torsion in `X / N`, including the infinitesimal
centre in characteristic two.

`centerCharacterRestriction_eq_zero_iff` gives the corresponding criterion
for an individual character. This is an internal consequence of the
published split existence and central isogeny theorems, the actual
centre and torus-kernel comparisons, and the diagonalizable functor.
