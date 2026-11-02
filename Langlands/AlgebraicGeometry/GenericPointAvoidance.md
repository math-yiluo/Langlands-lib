# Generic points under maps, and prime avoidance

Internal infrastructure.
- `mem_genericPoints_iff`: in a sober `T₀` space, Mathlib's `genericPoints` (generic points
  of irreducible components) are exactly the points without proper generalization.
- `mem_genericPoints_of_generalizingMap`: generalizing maps, for example flat morphisms of
  schemes, send generic points to generic points.
- `mem_genericPoints_of_isDiscrete_fibre`: continuous maps with discrete fibres, for example
  locally quasi-finite morphisms, reflect generic points.
- `PrimeSpectrum.exists_basicOpen_of_finite` and `exists_basicOpen_of_finite` (prime
  avoidance, via `Ideal.subset_union_prime`): a finite set of points inside an open subset
  of an affine scheme lies in a basic open contained in that subset.
