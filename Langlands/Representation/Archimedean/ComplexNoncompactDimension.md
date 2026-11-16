# The dimension of the filtration levels

Fix `i < r`; `rootUnit hir z = 1 + z E_{r,i}` is lower unipotent.

## Definitions

- `rootPos hlt = (r, i)` among the positions `Lw n`; `LwRest hlt` the other positions;
  `extCoords m`: extension of `m : LwRest hlt → ℂ` by `0` at the root position.
- `slice z m = lowCoords (rootMatrix i r z · nbMat (extCoords m))`, so that
  `nbUnit (slice z m) = rootUnit z · nbUnit (extCoords m)` (`nbUnit_slice`).
- `sliceMap T σ S N`: the linear map sending `F` to the family, indexed by `z ∈ S`, of the
  functions `m ↦ F(nbUnit (slice z m)) · D(slice z m)^N / ω(slice z m)`, with `D = ∏_m T_m` and
  `ω = ∏_m T_m^{σ_m}`.

## Results

- `card_Lw_mul_two`: `|Lw n| · 2 = n (n - 1)`.
- `nbUnit_lowCoords`: `nbUnit (lowCoords L) = L` for `L ∈ lowerUnipotent n ℂ`;
  `rootUnit_mem_lowerUnipotent`, `rootUnit_mul_neg`.
- `exists_rootUnit_mul_eq`: every lower unipotent `L` is `rootUnit z · nbUnit (extCoords m)`
  (take `z = L_{r,i}`).
- `isPolyMat_nbMat_extCoords`, `coord_slice_mem`: for fixed `z`, `slice z` is affine in `m`.
- `eq_zero_of_slices`: let `S` be a set on which every element of `bidegLT p q` vanishing on
  `S` is zero. A block-polynomial `F` of the principal series vanishing on `nbUnit (slice z m)`
  for all `z ∈ S` and all `m` vanishes on the lower unipotent group, hence is zero
  (`eq_zero_of_eqOn_lowerUnipotent`, module `ComplexLowerUnipotentRestriction`).
- `weight_ne_zero`, `gram_pow_ne_zero`: `ω` and `D^N` do not vanish for positive real `T_m`.
- `finrank_filtrationLevel_le`: for such `S`, `filtrationLevel N` is finite-dimensional and
  `finrank ≤ |S| (c (N + 1) + 1)^{n(n-1)-2}`. The map `sliceMap` restricted to the level takes
  values in `S → degLE (LwRest hlt) (c (N + 1))` (on the slice it equals `P ∘ slice z`) and is
  injective by `eq_zero_of_slices`; `LwRest hlt` has `n(n-1)/2 - 1` positions, hence
  `n(n-1) - 2` real coordinates, and `finrank_degLE_le` applies.

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
