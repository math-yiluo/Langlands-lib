# The Weyl element of the rank-one open-cell relation

Author: Worker 4348.

Module `Langlands.Algebra.RankOneRelationWeyl`, namespace
`Langlands.Algebra.RankOneRelation.Data`.

This module is pure group theory over a field `k` and a group `H`. It extends the published
module `Langlands.Algebra.RankOneRelationIdentities`, which defines the structure
`RankOneRelation.Data k H`. That structure has additive maps `xp xm : k → H`, a hom
`h : kˣ →* H`, the action `h t * xm c * (h t)⁻¹ = xm (t⁻² c)`, and the open-cell relation
`xp X * xm Y = xm (u⁻¹ Y) * h u * xp (u⁻¹ X)` for every unit `u = 1 + X Y`. That module also
defines `w c = xm (-c⁻¹) * xp c * xm (-c⁻¹)` and proves `w v = h v * w 1`
(`w_eq_h_mul_w_one`). In `SL₂`, `w(1)` is the matrix `[[0, 1], [-1, 0]]`.

## Results

- `w_inv c`: `(w c)⁻¹ = w (-c)`. Expand `w` and use `xp_neg`, `xm_neg`.
- `w_one_mul_self`: `w 1 * w 1 = h (-1)`. By `w_mul_w_one_inv` at `v = -1`,
  `w(-1) (w 1)⁻¹ = h(-1)`. Since `w(-1) = (w 1)⁻¹` by `w_inv`, this says
  `(w 1)⁻¹ (w 1)⁻¹ = h(-1)`. Invert both sides, using `h(-1)⁻¹ = h(-1)`; the latter holds
  because `h(-1) h(-1) = h(1) = 1`.
- `w_one_conj_h c`: `w 1 * h c * (w 1)⁻¹ = (h c)⁻¹` for every unit `c`.
  1. By `w_eq_h_mul_w_one` at `c` and at `-c`, together with `w_inv`,
     `(h c * w 1)⁻¹ = h(-c) * w 1`.
  2. `h(-c) = h c * h(-1) = h c * (w 1 * w 1)`.
  3. Write `a = w 1` and `b = h c`. Step 1 gives `a b a a a = b⁻¹`.
  4. `a⁴ = h(-1)² = 1`, so `a b a⁻¹ = (a b a³) a⁻⁴ = b⁻¹`.
- `h_mul_w_mul_h_mul_w c₁ c₂`: `h c₁ * w 1 * (h c₂ * w 1) = h (-(c₁ c₂⁻¹))`. Rewrite the left
  side as `h c₁ * (w 1 * h c₂ * (w 1)⁻¹) * (w 1 * w 1)`. Then apply the two previous results.

The last result is used in module `Rational.LinkedRootOppositePairs`. There, every
opposite-pair product around a nontrivial point of a root subgroup has the form `h c * w 1`.
So the product of two such elements lies in the image of the coroot.

## Provenance

These are the `SL₂` identities `w(1)² = -1` and `w(1) diag(c, c⁻¹) w(1)⁻¹ = diag(c⁻¹, c)`.
Here they are derived from the abstract relation only. This is an internal helper and makes
no assertion about group schemes.
