# Reduction of the adjoint Hasse kernel to almost-simple groups

`NumberFieldAlmostSimpleAdjointGaloisHasseKernelStatement` asserts that
an everywhere locally trivial natural cocycle is trivial for an
almost-simple adjoint group over a number field. It uses the given
finite Galois field cover and its pullbacks at every place, in the
same universe as the adjoint Hasse kernel.

The internal theorem `numberFieldAdjointGaloisHasseKernel_of_almostSimple`
derives the adjoint kernel from this arithmetic premise. The published
almost-simple presentation of a semisimple group supplies the finite
family of factors. Each factor maps by a closed immersion, and the
presentation map is surjective. For an adjoint target these properties
make the presentation an isomorphism. Every factor is adjoint because
it is semisimple and its center is trivial by the product center formula.

Project the cocycle onto each factor and apply the arithmetic premise
using preservation of local triviality under coefficient maps. The
coordinate trivializations give a product trivialization, which the
inverse isomorphism transports to the original cocycle. The construction
also covers the empty product.
