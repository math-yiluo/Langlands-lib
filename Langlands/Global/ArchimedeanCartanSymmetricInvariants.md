# Fixed symmetric algebras and Cartan invariant restriction

Author: Worker 94.

This internal construction uses the actual symmetric algebras and conjugation
maps in `ArchimedeanCartanSymmetricAlgebra`. It defines actual fixed subalgebras
by requiring equality under every element of the specified group. The field
universe and natural rank are unrestricted.

`lieSymmetricCompactInvariants` consists of symmetric tensors fixed by every
element of the full standard infinite compact subgroup.
`cartanSymmetricCompactInvariants` is the corresponding fixed subalgebra of
the complementary symmetric algebra.
`lieSymmetricGroupInvariants` requires invariance under every actual
archimedean group element. Algebra automorphisms preserve sums, products and
scalars, so each fixed set is a complex subalgebra.

The equivariant complementary inclusion and projection restrict to algebra
homomorphisms `cartanCompactInvariantInclusion` and
`cartanCompactInvariantProjection` between the compact fixed subalgebras.
Their composite projection after inclusion is the identity, using the same
identity on the ambient symmetric algebras. Consequently this inclusion is
injective and this projection is surjective.

Full-group fixed elements are compact fixed elements.
`lieSymmetricGroupToCompactInvariants` is the induced inclusion.
`cartanGroupInvariantRestriction` composes it with the compact invariant
projection; its underlying value is the actual complementary symmetric
projection.

Surjectivity is proved only for the map between the two compact fixed
subalgebras. No surjectivity or finite-module assertion is made for
`cartanGroupInvariantRestriction`. These are symmetric tensors on vectors;
comparison with restriction of polynomial functions needs the separate
trace-duality identification. This module supplies no invariant averaging
operator, invariant restriction finiteness, PBW comparison, central
generation, admissibility or automorphic growth theorem.
