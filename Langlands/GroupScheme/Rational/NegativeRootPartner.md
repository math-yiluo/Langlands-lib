# The negative partner of a normalized simple-root parametrization

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.NegativeRootPartner`, namespace
`Langlands.GroupScheme.SplitPinning.NormalizedRootParametrization`.

Let `k` be a field, `G` an affine group scheme over `k`, `p` a split pinning of `G`, `a` a
simple root and `x : p.NormalizedRootParametrization a`. This module constructs a negative
root map linked to `x`. It identifies its values as the opposite factors of the values of
`x`.

## Construction

- `exists_linked`: there is a `LinkedRootParametrization` of `±a` (cocharacter `a^∨`) whose
  positive map is exactly `x.hom`. Start from the Library's linked parametrization
  `nonempty_linkedRootParametrization`. By `exists_eq_scaleHom_comp` (module
  `Reductive.LocalWeylNormalizationField`), its positive map is `scaleHom l ≫ x.hom` for
  some `l ≠ 0`. By `relationOver_scaleHom` and `scaleHom_one`, the pair
  `(x.hom, scaleHom l ≫ X.negative)` satisfies the rank-one relation. The rescaled negative
  map still represents the negative root group, via `SubgroupFunctor.range_iso_comp` with
  `scaleIso`. It is still equivariant of weight `-a`, by `comp_scaleHom` and the
  equivariance of `X.negative`.
- `linked` is a chosen such parametrization, and `linked_positive` records
  `linked.positive = x.hom`.
- `negPoint c`, written `y(c)` below, is its negative rational point `linked.xmPoint c`
  (module `Reductive.LinkedRootRationalRelation`).

## Results

- `pairing_root_coroot`: `⟨a, a^∨⟩ = 2`, from the root datum of the pinning.
- `xpPoint_linked`, `rootPoint_linked_positive`, `rootPoint_linked_negative`: the positive
  points of `linked` are the rational values of `x`, and the negative points are `y`, in
  both the `xpPoint` and `rootPoint` notations.
- `isOppositeFactorPair_unitPoint`: `(y(-1), y(-1))` is an opposite factor pair of `x(1)`.
  This is the published `isOppositeFactorPair_weylPoint`, with opposite pairs supplied by
  `splitPinnedOppositeFactorPairs`.
- `negPoint_mem`: `y(c)` lies in the root group of `-a`.
- `cocharacterPoint_mem_normalizerPoints`: cocharacter points of the torus normalize it.
  They centralize it, by `range_le_torusCentralizer` and `torusCentralizer_carrier_base`.
- `isOppositeFactorPair_rationalPoint c`: for every unit `c`, `(y(-c⁻¹), y(-c⁻¹))` is an
  opposite factor pair of `x(c)`. With the rank-one data `D` of `linked`, the triple product
  is `D.w c = D.h c * D.w 1` (`w_eq_h_mul_w_one`, module `Algebra.RankOneRelationIdentities`).
  Here `D.w 1` is the normalizing triple of the unit case, and `D.h c` is a cocharacter
  point.
- `negPoint_zero`: `y(0) = 1`.
- `eq_negPoint_of_isOppositeFactorPair c hq`: every opposite factor pair of `x(c)` is
  `(y(-c⁻¹), y(-c⁻¹))`. This uses uniqueness of opposite pairs,
  `IsOppositeFactorPair.eq`. In particular `y` depends only on `x`, not on the choice of
  `linked`.

## Provenance

Internal construction from published Library results. In `SL₂` it is the familiar fact that
`x₋(-c⁻¹) x₊(c) x₋(-c⁻¹)` is the Weyl element `diag(c, c⁻¹) w`.
