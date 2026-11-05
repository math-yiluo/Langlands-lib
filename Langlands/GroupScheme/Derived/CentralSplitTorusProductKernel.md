# The full kernel of compatible derived and central split factors

Author: Worker 1482.

This internal auxiliary development concerns the actual multiplication from two
compatible split factors to a split torus. It is derived from the Library's
published full central-intersection finiteness theorem, without a further
literature assertion.

`DerivedCentralSplitTorusProductKernelFinitenessStatement.{u}` states the
universal finite-kernel assertion below. The module proves it as
`derivedCentralSplitTorusProductKernelFiniteness`; it also exposes the direct
lemma `isFinite_kernel_derivedCentralSplitTorusProduct`.

For any product homomorphism, if the second factor map is monic, projection of
its full scheme-theoretic kernel to the first factor is monic. The proof compares
both coordinates on arbitrary test schemes: equality of the first coordinates
and the kernel equation give equality after the second factor map, and monicity
then gives equality of the second coordinates.

For a connected reductive field group and an actual derived inclusion, the
derived coordinate of a multiplication kernel point maps to the inverse of the
central coordinate in the ambient group. Thus it belongs to the preimage of the
full center. The published `derivedCentralIntersectionFiniteness` supplies a
finite closed representative of this subgroup functor. The kernel maps
monomorphically to that representative. The kernel is affine and of finite type,
being a closed subgroup of a product of split tori. Its monomorphism to the finite
representative is locally quasi-finite, so its structure map is locally
quasi-finite. Quasi-compactness and the Artinian field base imply finiteness.

All these comparisons use the full functors of points and therefore include
nonreduced tests. The field, characteristic and universe are arbitrary.
Maximality of the split factors is unnecessary for the kernel assertion.
This module does not prove surjectivity of multiplication or the exact
`DerivedCentralSplitTorusProductStatement`.
