# Basis integrality versus integrality in the local tensor decomposition

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, w a finite place of K and K_w = `w.adicCompletion K`. An element x of K_w ⊗_K L can be called integral in two ways. Its coordinates in the fixed K-basis of L may lie in the valuation ring of K_w. Or its image in each completion of L above w, under the local tensor decomposition, may lie in the valuation ring there. This file shows that the two notions agree outside an explicit finite set of places, and likewise for units.

## Definitions

- `finitePlaceLocalTensorDecompositionComponent w wL x`: the component of x in the completion of L at an extension wL of the w-adic absolute value. `..._tmul` gives it on pure tensors.
- `RelativeLocalTensorDecompositionIntegralAt w x`: every component of x lies in the valuation ring of its completion. `RelativeLocalTensorDecompositionIntegralUnitAt` asks this of a unit and of its inverse.
- `scaledRelativeBasisDiscriminantInteger`: the discriminant of the scaled basis of the lattice file, as a nonzero element of 𝓞 K. `scaledRelativeBasisDiscriminantBadPlaces` is the finite set of primes dividing it. Outside this set the discriminant has w-adic absolute value 1.
- `integralTensorComparisonBadPlaces`: the union of `integralTensorBadPlaces` and the discriminant bad places.

## Results

- `relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem`: outside `integralTensorBadPlaces`, an element satisfying the library's basis-integrality predicate `RelativeBasisIntegralAt` is integral in every local tensor factor. The unit version is `relativeBasisIntegralUnitAt_imp_..._of_notMem`.
- `scaledRelativeTensorCoordinates_isIntegral_of_localTensorDecompositionIntegral`: outside the discriminant bad places, local tensor integrality makes the coordinates of x in the scaled basis integral over the valuation ring of K_w.
- `localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem` and its unit version: outside `integralTensorComparisonBadPlaces`, local tensor integrality implies basis integrality.
- `relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem` and `relativeBasisIntegralUnitAt_iff_localTensorDecompositionIntegralUnit_of_notMem`: outside `integralTensorComparisonBadPlaces`, the two notions are equivalent, for elements and for units.

## Proofs

The forward direction expands x in the basis: coefficients and, outside the bad set, basis vectors land in the valuation rings. For the converse, take the scaled basis vectors b_i. The traces of b_i b_j and of x b_i are integral by `isIntegral_trace_tensor_of_components`, and the inverse discriminant is integral outside the discriminant bad places. Cramer's rule (`basis_coord_isIntegral_of_integral_traces`) makes the scaled coordinates integral. The original coordinates are these times the integer scale d, and |d| ≤ 1.

## Points to watch

- Every comparison holds only outside a finite set of places. This set depends on the fixed basis and on choices made in the lattice file, so it is not canonical.
- The converse only uses that w avoids the discriminant bad places, although its hypothesis is stated with the larger set.
- The components are taken in the absolute-value model of the completions. The input, over Mathlib's adic completion of K, first passes through the inverse of `relativeFinitePlaceLocalTensorAlgEquiv`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/LocalTensorDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `5bb074c8b23c408a0ee6562380d89885aad8d5e5bc586db604563bb72c57994b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
