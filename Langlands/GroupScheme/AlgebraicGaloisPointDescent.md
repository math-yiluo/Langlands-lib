# Effective affine-point descent over arbitrary Galois extensions

Let `k` and `L` be fields in the same arbitrary universe, with a `k`-algebra
structure on `L` and `IsGalois k L`. Let `G/k` be an actual affine group scheme.
There is no finite-degree assumption. The point carriers, coefficient extension,
coefficient conjugation and fixed subgroup are those already defined in
`GaloisPointDescent`.

The pinned Mathlib infinite-Galois fixed-field theorem
`InfiniteGalois.mem_range_algebraMap_iff_fixed` puts every coordinate of an
automorphism-fixed point in the image of `k`. The coordinate computation is
the existing `coordinates_conjugate`. Choosing the base-field preimage of
each value gives `algebraicDescendValue`. Injectivity of `algebraMap k L`
proves the algebra-map laws for `algebraicDescendCoordinates`.

The existing affine-coordinate equivalence reconstructs an actual scheme
point, `algebraicDescend`. Its extension recovers the original fixed point,
as proved by evaluating every coordinate. The reverse recovery follows from
the published injectivity of coefficient extension. Thus
`algebraicFixedEquiv` is an actual multiplicative equivalence between base
points and the existing fixed subgroup. Its forward map is exactly the
existing `extend`, and its inverse has the stated recovery formula.
`mem_range_extend_iff_algebraic` gives the corresponding image criterion.

This is an internal generalization of the coordinate construction in
`GaloisPointDescent`, replacing its finite-Galois fixed-field step by the
infinite-Galois theorem. It leaves the published finite-degree API available.
It assumes no topology, smoothness, reductivity, integral model or building
data. It supplies no integral-model classification or building comparison.
