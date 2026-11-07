# Realized torus characters form a submonoid

Worker 1161. This module contains internal definitions supporting the
positive-multiple step of dominant highest-weight existence. Let `i : H → G` and
`j : U → G` be homomorphisms of group schemes over a field, with `G` and `H` affine
over the base.

- `IsRealizedCoordinate i j χ f` says three things about the coordinate `f` of `G`:
  it lies in the left covariant subspace along `i` for the coordinate of the
  rational character `χ` of `H`; it is right invariant along `j` on every relative
  test scheme; and its counit is one. In the application, `H` is a negative
  dynamic Borel subgroup and `j` is the inclusion of the positive contracting
  subgroup. A realized coordinate is then the classical normalized function
  `f(b g u) = χ(b) f(g)`, `f(1) = 1`, of Milne, *Algebraic Groups* (2017), §22.
- `isRealizedCoordinate_zero`: the constant coordinate `1` realizes the zero
  character.
- `IsRealizedCoordinate.add`: products of realized coordinates realize sums of
  characters. This uses the published `mul_mem_leftCovariantSubspace` and
  `characterCoordinate_add`, and multiplicativity of point evaluation.
- `realizedSet tH i j`, for `tH : T → H` from a commutative group scheme `T`, is
  the additive submonoid of `characterLattice T` of restrictions along `tH` of
  realized characters of `H`.
- `isRealizedCoordinate_characterCoordinate`: let `ψ` be a rational character of
  `G` that is trivial on the points of `U` through `j`. Then its own coordinate
  realizes the restriction `ψ ∘ i`. Point evaluation of a character coordinate is
  the character value, which is multiplicative.

These are derived definitions; they assert no existence.
