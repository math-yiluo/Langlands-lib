# Points of an affine group scheme over a ring split by an idempotent

Module `Langlands.GroupScheme.AffineIdempotentPoints`, namespace
`Langlands.GroupScheme.IdempotentPoints`. It imports
[`AffinePointProducts`](AffinePointProducts.md) (points over a product ring, which brings in
coordinate evaluation `affinePointEvaluation`) and
[`Algebra.EtaleGraphIdempotent`](../Algebra/EtaleGraphIdempotent.md).

## Provenance

Provenance: derived/internal. For an idempotent `e` of `C`, `Spec C` is the disjoint union of
`Spec C/(1 - e)` and `Spec C/(e)`. So the points of an affine group scheme over `C` are pairs
of points over the two factors. This module records that standard fact and the resulting
"projection to the `e`-component" for use in
[`Reductive.WeilFactorProjection`](Reductive/WeilFactorProjection.md) and
[`Reductive.WeilFactorUniquenessReduction`](Reductive/WeilFactorUniquenessReduction.md).

## Setting

`R : Type u` is a commutative ring, `K : GroupScheme (Spec R)`, and `C` is an `R`-algebra.
Points are `K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)`. Most results assume
`IsAffine K.X.left`.

## Declarations

- `fst K e`, `snd K e`: restriction of points along the quotient maps `C → C/(1 - e)` and
  `C → C/(e)` (`K.affinePointMap` of `Ideal.Quotient.mkₐ`). These are exactly the maps in
  [`WeilFactorIdempotentRigidityStatement`](Reductive/WeilFactorIdempotentRigidityStatement.md).
- `ev K x a`: the value at `x` of the global function `a` (`affinePointEvaluation`).
  `ev_map` is the naturality of evaluation, and `ev_injective` says points are determined by
  their values.
- `ext_of_idempotent`: a point over `C` is determined by its two restrictions, because
  `(1 - e) ∩ (e) = 0`.
- `crt R he : C ≃ₐ[R] C/(1 - e) × C/(e)` (Mathlib's `AlgEquiv.prodQuotientOfIsIdempotentElem`)
  and `crt_symm_mk`: the inverse sends `(ū, w̄)` to `e u + (1 - e) w`.
- `mixQ K he g₁ g₂`: the point over `C` glued from points over the two factors, built from
  `affinePointPair` and `crt`. `fst_mixQ` and `snd_mixQ` give its restrictions.
- `mix K he g h = mixQ (fst g) (snd h)`. `ev_mix` gives its values `e u + (1 - e) w`, and
  `fst_mix`, `snd_mix` give its restrictions.
- `projAux K he`, `proj K e`: the homomorphism `g ↦ mix g 1`, which keeps the `e`-component and
  kills the `(1 - e)`-component (`proj` is trivial when `e` is not idempotent). Lemmas:
  `proj_eq`, `proj_apply`, `fst_proj`, `snd_proj`, `ev_proj` (values `e u + (1 - e) ε(a)`),
  `eq_proj_iff` (`y = proj e g ↔ fst y = fst g ∧ snd y = 1`), `proj_map` (naturality along
  `f : C →ₐ C'` with `f e = e'`), `proj_proj` (`proj e ∘ proj f = proj (e f)`), `proj_one`,
  `proj_zero`, `proj_conj` (`proj` commutes with conjugation).
- `quotEquiv`: if `mu : C →ₐ[R] D` is surjective with kernel `(1 - e)`, the induced
  `D ≃ₐ[R] C/(1 - e)`. Lemmas `quotEquiv_apply` and `quotEquiv_symm_mk`.
- `factorEquiv K he hmu hker : (snd K e).ker ≃* K(D)`: points over `C` that are trivial on the
  `(1 - e)`-component are exactly the points over `D`. The forward map is
  `K.affinePointMap mu` (`factorEquiv_apply`). The inverse is
  `g ↦ mixQ (quotEquiv-image of g) 1`.

All identities are proved through coordinate evaluation (`ev_injective`), using the formula
`e u + (1 - e) w` and ring identities, except `ext_of_idempotent`, which uses the ideal
intersection.
