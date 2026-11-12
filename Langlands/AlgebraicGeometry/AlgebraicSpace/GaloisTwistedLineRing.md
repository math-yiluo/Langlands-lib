# The rings of the Galois-twisted line

Author: Worker 105.

This is ring-theoretic support for Conrad's Example 5.13 (printed p.20). It contains no
statement from the paper.

## The construction

Conrad's space is the quotient `L'/G` of the affine `K'`-line `L'` by the étale group `G`
obtained from `(Z/2Z)_L` by deleting the non-identity point over the origin. This module
describes the groupoid of that action in ring terms:

- The line is `A = K'[X]`.
- The relation ring is `RelationRing K' = K'[X] × K'[X, 1/X]`. The second factor is
  `PuncturedRing K' = Localization.Away X`.
- `conjPoly D` applies `σ` to the coefficients and fixes `X`. `conjPunct D` is its extension to
  the punctured ring.
- `tStar` and `sStar D`, both `K'[X] → RelationRing K'`, are the identity on the first factor.
  On the second factor:
  - `tStar` is the localization map;
  - `sStar D` is the localization map after `conjPoly D`.

  The first factor is the identity component of the action. The second factor is the
  non-identity component over the punctured line, acting through `σ`.
- `swapStar D` exchanges `tStar` and `sStar D` and is an involution (`swapStar_comp_tStar`,
  `swapStar_comp_sStar`, `swapStar_swapStar`).

## Ring maps out of the relation ring

Let `x z : K'[X] →+* Γ`.

- `pairIdem D x z` is `splitIdem` of the restrictions of `x` and `z` to `K'`.
- `pairUnit D x z = e + (1 − e) · x(X)`, where `e = pairIdem D x z`.
- `SameBase K x z` means that `x` and `z` agree on `K` and on `X`.

The main results:

- `sameBase_of_hom` and `isUnit_pairUnit_of_hom`: every `φ : RelationRing K' →+* Γ` gives a pair
  `(φ ∘ tStar, φ ∘ sStar)` over the same base point whose `pairUnit` is a unit. Moreover
  `φ (1, 0)` is the idempotent `pairIdem` (`pairIdem_of_hom`, proved with `splitIdem_unique`).
- `hom_ext`: such `φ` is determined by the two composites. Every element of the relation ring is
  written through `tStar`, the idempotent `(1, 0)` and the map `jHom` (`relationRing_decomp`).
- `relHom D hb hu`: conversely, a pair over the same base point with `pairUnit` a unit comes from
  a ring map. It is built as a "corner" map `cornerHom` on the two factors. On the second factor
  it uses the point `modPoint`, which sends `X` to `pairUnit`, so that it extends to the
  localization. `relHom_comp_tStar` and `relHom_comp_sStar` compute its two composites.
- `pairIdem_self`, `pairIdem_trans` and `isUnit_pairUnit_trans` give reflexivity and
  transitivity at the level of these pairs. The transitivity certificate is an explicit
  `linear_combination`.
