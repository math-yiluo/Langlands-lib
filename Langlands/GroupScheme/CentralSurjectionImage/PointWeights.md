# Coordinate bialgebras and weight functionals of points over group algebras

Author: Worker 1387.

This internal module works over a field `k : Type u` with an affine group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` (`[IsAffine G.X.left]`); `G` need not
be commutative. Points of `G` with coefficients in a `k`-algebra `S` are the
Library's `Lie.AffinePoints G S`, and `CocharacterDatum.coord x` is the
coordinate algebra map of such a point, out of the chosen coordinate algebra
`CocharacterDatum.coordAlgebra G`.

## Coordinates

`corep G` is the published corepresentation
`AffineLinearEmbedding.corepresentableBy G (coordIso G)`; its inverse
classification map is exactly `coord`. `comul G` and `counit G` are the
comultiplication and counit `AffineLinearEmbedding.comul` and
`AffineLinearEmbedding.counit` of this corepresentation.

- `coord_mul`: `coord (x * y)` is `productMap (coord x) (coord y) ∘ comul G`,
  that is, products of points are convolutions. This is
  `AffineLinearEmbedding.homEquiv_symm_mul`.
- `coord_one`: the identity point has coordinate map `algebraMap ∘ counit G`
  (`AffineLinearEmbedding.homEquiv_symm_one`).

## Multiplicative points and weights

For an additive commutative group `Λ` and a point `p` over `S[Λ]`:

- `expMapG g` changes exponents along `g : Λ →+ Λ'`, and `expMapG_expMapG`
  composes such changes.
- `IsMultG p` says
  `expMapG diag p = expMapG inl p * expMapG inr p`. It is the definition of
  `CocharacterDatum.IsMult` for an arbitrary, possibly noncommutative, affine
  group scheme, and agrees with it definitionally on `Z.toGrp`.
  `IsMultG.expMapG_zero` derives `expMapG 0 p = 1` by applying the zero
  exponent change to the defining identity.
- `weight p γ` is the `k`-linear functional `b ↦ (coord p b).coeff γ` on the
  coordinate algebra. `eq_of_weight_eq` says points are determined by their
  weights; `weight_coeffMap` computes the weights of a coefficient change;
  `weight_one` computes those of the identity point.
- `conv f g` is the convolution `mul' ∘ (f ⊗ g) ∘ comul G` of two functionals.
- `IsMultG.conv_weight`: for a multiplicative point,
  `conv (weight p γ) (weight p δ) = if γ = δ then weight p γ else 0`. The proof
  takes the `(γ, δ)`-coefficient of the coordinate maps of both sides of
  `IsMultG p` and uses `coeff_mapDomain_diag` and
  `coeff_productMap_inl_inr` (from `GroupAlgebraCoeff`).
- `IsMultG.sum_weight`: the weights of a multiplicative point sum to the counit,
  from `expMapG_zero`.
- `IsMultG.eq_one_of_weight_eq_zero`: a multiplicative point all of whose
  nonzero weights vanish is the identity point.

This is internal infrastructure. It formalizes the standard description of a
homomorphism from a diagonalizable group as a system of orthogonal convolution
idempotents; no literature result is attributed to it.
