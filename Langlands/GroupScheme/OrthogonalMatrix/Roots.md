# Maximality of the diagonal torus of the split orthogonal group and its roots

This internal module shows that the diagonal torus of the split orthogonal group
`OrthogonalMatrix.groupScheme l k` over a field `k`, factored through the identity
component, is a maximal torus there, and computes its roots. The proofs follow the
published module `SymplecticMatrix.Roots`, with the orthogonal Lie condition in place
of the symplectic one.

## Indices and the swap form of the Lie condition

- `index x`: the index `a` of `inl a` and of `inr a`; `index_swap`,
  `eq_or_eq_swap_of_index_eq` (two indices with the same `index` are equal or swapped),
  `swap_ne_self`, `eq_swap_iff`.
- `weightCoord_swap`: `w(swap x) = -w(x)`, where `w(inl a) = e_a` and `w(inr a) = -e_a`.
- `polarMatrix_apply`: the polar matrix `J` of the hyperbolic form has entry `1` at
  `(z, swap z)` and `0` elsewhere, so `(Y J) x y = Y x (swap y)` and
  `(J M) x y = M (swap x) y`.
- `isAlt_lie_iff_swap`: `Y Q + Q Yᵀ` is alternating exactly when
  `Y x (swap y) + Y y (swap x) = 0` for all `x, y` and `Y x (swap x) = 0` for all `x`.
- `isAlt_diagonal_lie`: `diag(d, -d)` satisfies the Lie condition.
- `isAlt_rootVector_lie`: the root vector `E_{x y} - E_{swap y, swap x}` satisfies it.
- `lieMatrix_swap_add`, `lieMatrix_swap_self`, `lieMatrix_inr_inr`: the same relations
  for the matrix of a Lie algebra element.

## Maximality over a field

- `mem_weightSpace_zero_iff`: the zero weight space consists of the Lie algebra
  elements whose matrix is diagonal.
- `zeroWeightCoord`, `zeroWeightCoord_bijective`: the upper-left diagonal entries give a
  linear isomorphism from the zero weight space to `k^l`, using `lieMatrix_inr_inr` for
  the lower-right entries and `isAlt_diagonal_lie` for surjectivity.
- `finrank_weightSpace_zero`: the zero weight space has dimension `|l|`.
- `identityTorus l k`: the diagonal torus factored through the identity component
  (published `IdentityComponent.torusHom`); `identityTorus_comp`,
  `isClosedSubgroup_identityTorus`, `isSplitSubtorus_identityTorus`.
- `isMaximalTorus_identityTorus`: it is a maximal torus of the identity component, by
  the published criterion `isMaximalTorus_of_finrank_zeroWeight` (the zero weight space
  has the dimension of the torus) together with `IdentityComponent.finrank_weightSpace`.
- `roots_identityTorus`: its roots are those of the diagonal torus in the whole group
  (published `IdentityComponent.roots_torusHom`).

## Roots

- `mem_roots_iff`: a character `χ` is a root of the diagonal torus exactly when its
  coordinates are `w(x) - w(y)` for indices `x, y` with `index x ≠ index y`, that is,
  `χ = ±e_a ± e_b` with `a ≠ b`. A nonzero Lie algebra element in the weight space has
  a nonzero entry at some `(x, y)`, which forces `χ = w(x) - w(y)`; `x = y` would make
  `χ` zero and `y = swap x` is excluded by `lieMatrix_swap_self`. Conversely the root
  vector `E_{x y} - E_{swap y, swap x}` lies in the weight space of `w(x) - w(y)`.
