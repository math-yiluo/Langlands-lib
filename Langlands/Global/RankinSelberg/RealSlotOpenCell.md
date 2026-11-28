# The open cell of the slot Levi subgroup

Lean module: `Langlands.Global.RankinSelberg.RealSlotOpenCell`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `CoordM`, `lowerM` and `lowerMGL`
are from `RealLeviLeviBorel`, `CoordC` from `RealLeviChartIntegrable`, `lowerCGL` from
`RealLeviTwoBlock`; the slot matrices are those of `RealSlotMatrices`.

## The block index

- `SlotSet.blockIdx S i` is the number of positions before `i` that do not start a slot. It is
  monotone (`blockIdx_monotone`); the two positions of a slot have the same index
  (`blockIdx_second`), and two other positions `j < i` have `blockIdx j < blockIdx i`
  (`blockIdx_lt_of_lt`, `eq_of_blockIdx_eq`). Thus the blocks of `blockIdx` are the slots and the
  single positions outside the slots. `blockIdx_perm`: it is invariant under the slot swap.

## The coordinates inside the blocks

- `coordMEquiv : CoordM S.blockIdx ≃ S.starts` identifies the coordinates inside the blocks with the
  slots: the only such coordinate of the slot `p` is the entry `(p + 1, p)`
  (`coordMEquiv_symm_val`). `slotOfM Z` is `Z` read as slot coordinates;
  `measurePreserving_slotOfM` and `integral_comp_slotOfM`: this preserves Lebesgue measure.
- `swap2_mul_upper2_mul_swap2`: `[[0, 1], [1, 0]] [[1, x], [0, 1]] [[0, 1], [1, 0]] =
  [[1, 0], [x, 1]]`. `lowerMGL_eq`: the block lower unitriangular matrix of the slot set is
  `lowerMGL S.blockIdx Z = swapGL S · unip S (ext (slotOfM Z)) · swapGL S`.

## Conjugating the opposite radical by a block permutation

For a block function `cl` with values in a linear order and a permutation `σ` of the positions
that preserves it (`cl ∘ σ = cl`):

- `permCoord σ hσ` permutes the coordinates of `CoordC cl`, and, for monotone `cl` (`hcl`),
  `permutation_mul_lowerCGL` gives
  `P_σ · lowerCGL hcl X = lowerCGL hcl (X ∘ permCoord σ hσ) · P_σ` for the permutation matrix `P_σ`
  (`permutation_conjugate_entry`).
- `measurePreserving_comp_permCoord` and `integral_comp_permCoord`: `X ↦ X ∘ permCoord σ hσ`
  preserves Lebesgue measure.
