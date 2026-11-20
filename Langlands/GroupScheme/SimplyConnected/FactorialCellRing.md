# The coordinate ring of the big-cell source over a field

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, describes the source
`𝔾ₐᵐ × 𝔾ₘ^I × 𝔾ₐⁿ` of the big-cell map over a field `k` as the spectrum of an
explicit factorial ring. Here `m` and `n` count the negative and positive roots
and `I` indexes the coordinates of a split torus (a finite type).

## The ring

- `CellVar I m n = Fin m ⊕ Fin n ⊕ I` are the coordinates. `torusMonomial` is
  the product of the torus coordinates; it is nonzero (`torusMonomial_ne_zero`).
- `CellRing k I m n` is the localization of `MvPolynomial (CellVar I m n) k` away
  from `torusMonomial`, that is, `k[v, w, t, t⁻¹]`. It is a domain and a unique
  factorization monoid, since localizations of the factorial polynomial ring are
  factorial (Mathlib instances).
- `negVar r`, `posVar r` and the units `torusVar i` (`isUnit_torusVar`,
  `torusVar_val`) are the coordinates `v_r`, `w_r` and `t_i`.
- `ringHom_ext`: ring maps out of `CellRing` that agree on `k` and on all
  coordinates are equal. `liftHom f v w t` is the ring map with scalars `f`
  and coordinates `v`, `w`, `t` (the `t i` units). Its values are given by
  `liftHom_algebraMap`, `liftHom_comp_algebraMap`, `liftHom_negVar`,
  `liftHom_posVar` and `liftHom_torusVar`.
- `prime_negVar`: each `v_r` is prime. It is prime in the polynomial ring
  (`MvPolynomial.X_prime`), and its prime ideal misses the powers of
  `torusMonomial`: evaluate at `v_r = 0` and all other coordinates `1`.
- `shiftHom r s` is the ring endomorphism sending `v_r ↦ v_r + s` and fixing the
  other coordinates (`shiftHom_negVar_self`, `shiftHom_negVar_of_ne`,
  `shiftHom_posVar`, `shiftHom_torusVar`). By `shiftHom_comp`, `shiftHom r s` is
  inverse to `shiftHom r s'` when `shiftHom r s s' + s = 0`. `shiftEquiv r` is
  the automorphism `v_r ↦ v_r + 1` (`shiftEquiv_negVar`).
- `prime_one_add_negVar`: each `1 + v_r` is prime, being the image of the prime
  `v_r` under `shiftEquiv r`.

## The scheme

- `cellSpec k I m n` is `Spec (CellRing k I m n)` as an object over
  `Spec k`.
- `pointRing z : CellRing →+* Γ(W.left, ⊤)` is the ring map of a point
  `z : W ⟶ cellSpec`. It is compatible with scalars
  (`pointRing_comp_algebraMap`) and injective in `z` (`pointRing_injective`).
  By `exists_pointRing_eq`, every ring map compatible with scalars arises this
  way (the `Γ ⊣ Spec` adjunction).
- `specNeg r`, `specPos r` and `specTorus` are the coordinate functions and the
  torus coordinate on `cellSpec`. `cellCoordHom : cellSpec ⟶ cellObj k I m n`
  is the resulting map to the cell source of
  `Langlands.GroupScheme.LocalSplitCell` (product of the vector group
  `𝔾ₐᵐ`, the split torus and `𝔾ₐⁿ`).
- `pointsEquiv_comp_specTorus` and `coordTriple_comp_cellCoordHom` compute the
  coordinates of `z ≫ cellCoordHom` through `pointRing z`.
- `bijective_comp_cellCoordHom`: composition with `cellCoordHom` is a bijection
  on `W`-points, for every `W` over `Spec k`. This combines
  `LocalSplitBigCell.coordTriple_bijective` with `ringHom_ext` and `liftHom`.
- `isIso_cellCoordHom`: `cellCoordHom` is an isomorphism (Yoneda).

Provenance: internal; elementary commutative algebra and the functor of points
of affine space and the split torus.
