# Coordinates of the three-block open cell

Module `Langlands.Representation.Shahidi.OpenCellThreeBlockCoordinates`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- Entry formulas by index values: `blockSum_apply_val`, `upper_apply_val`, `swapRank_apply`,
  `blockWeylPermutation_val`, `blockWeyl_apply_val`, `blockWeyl_mul_apply`,
  `intertwiningUnipotent_apply`, `sum_intertwiningUnipotent_row`.
- `headColumns d t Y`: the first `d + 1` columns of `Y ∈ M_((t+1)×(1+(d+1)))`;
  `shearColumn d t Y z = [Y_b - Y_a z; z]` with `Y_a = headColumns Y` and `Y_b` the last column.
- `reindex_swapRank_unipotent`, `reindex_blockWeyl_mul_swapRank`, and the main identity
  `reindex_threeBlock`: under the reassociation
  `GL_((1 + (d+1)) + (t+1)) ≅ GL_(1 + ((d+1) + (t+1)))`,

  `diag(w' u'(z), 1) · w u'(Y) ↦ diag(1, w'' u''(Y_a)) · w̃ u'(shearColumn Y z)`,

  where `w', u'` are for the blocks `(1, d+1)`, `w, u'` for `(d+2, t+1)`, `w'', u''` for
  `(d+1, t+1)` and `w̃, u'` for `(1, d+t+2)`.

## Provenance

Direct matrix computation: both sides are the long Weyl element of the three-block parabolic
times the same unipotent matrix, in two coordinate systems.
