# Cocharacter data from a single point over an algebraically closed field

Author: Worker 1387.

This internal module, in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`, works over a field `k : Type u`.

## Universal points and character coordinates

For an affine group scheme `G`:

- `univ G` is the universal point `(coordIso G).hom` over the coordinate algebra.
  `coord_univ` shows its coordinate map is the identity, and
  `affineMap_coord_univ` recovers every point `x` as the coefficient change of
  `univ G` along `coord x`.

For an affine commutative group scheme `Z` and a character
`χ : characterLattice Z`:

- `charCoord χ` is the coordinate function `χ(univ)`.
  `characterValue_eq_coord` says `χ(x) = coord x (charCoord χ)` for every
  point `x`.
- `comul_charCoord` and `counit_charCoord`: `charCoord χ` is grouplike. The
  first applies `characterValue_mul` to the two universal points over
  `B ⊗ B`, using `coord_mul` and `productMap_includeLeft_includeRight`.
- `pointOfCoord f` is the point with a prescribed coordinate map `f`, and
  `coord_pointOfCoord` says so.

## The datum

`exists_datum_of_point χ x` takes an algebraically closed field `K` over `k` and
a point `x` of `Z` over `K`. It gives a point `p` over `K[Kˣ]` (exponent group
`Additive Kˣ`) with `CocharacterDatum.IsDatum χ (Additive.ofMul (χ x)) p`. The
proof equips the coordinate algebra with the bialgebra structure
`AffineLinearEmbedding.bialgebra (corep Z.toGrp)`. It then applies
`EigenGrading.exists_grading` to `e = coord x` with the left convolution inverse
`coord x⁻¹`, obtained from `coord_mul` and `coord_one`. `p` is the point whose
coordinate map is the resulting grading `ψ`. Comultiplicativity of `ψ` is
`IsMult p`, and `ψ (charCoord χ) = X^{χ(x)}` gives the value.

This is internal derived content; no literature result is attributed to it.
