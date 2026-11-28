# The slot data of a real block list

Lean module: `Langlands.Global.RankinSelberg.RealSlotBlockData`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `realInducedBlockAt`,
`realPositionExponent`, `realPositionBlockExponent`, `induced_at`, `exponent_re_eq`, `slots`,
`mkSlot`, `inClass_slots` and `exists_hasDegree` are from `StandardModule`,
`PrincipalSeriesGramFormula` and `RealInducedStandardBound`; `RealPrincipalSeries.expand` replaces
each induced block by its two position characters (module `RealPrincipalSeriesFactors`), and
`canonicalJacquetMap a p z` is the canonical Jacquet map of the character list `characterList p z`
(module `RealGodementCanonicalCoefficient`).

The module attaches to a block list `ds` of rank `r + 1` the slot set of its induced blocks of
nonzero weight, and checks the hypotheses of `canonical_tempered_slot_bound` for the exponents of
the expansion of `ds` and the standard vectors of `ds`.

## The slots of the induced blocks of nonzero weight

- `slotWeight ds p` is the absolute weight of the induced block of `ds` with first position `p`, and
  `0` if there is none (`slotWeight_of`, `slotWeight_of_none`, `exists_of_slotWeight_ne_zero`).
- `blockSlots ds hr` is the slot set of the positions `p` with `slotWeight ds p ≠ 0`
  (`mem_blockSlots`, `blockSlots_weight_ne_zero`). Its slots are disjoint because the position after
  the first position of an induced block is not the first position of another one
  (`induced_at`).

## The exponents of the positions

- `realPositionExponent_expand`: the expansion has the same position exponents as `ds`.
- `realPositionBlockExponent_eq_zero`: if all block exponents of `ds` have real part `0`, so do the
  block exponents of all positions. `not_induced_pred`: the position before the first position of
  an induced block is not the first position of one.
- `realPositionExponent_re`: for a block list with imaginary block exponents,
  `Re (realPositionExponent ds i) = halfWeights (blockSlots ds hr) (slotWeight ds) i`. An induced
  block with exponent `ν` and weight `k` has the position exponents `ν ± |k|/2` (`induced_at`); the
  other positions have the real part of their block exponent (`exponent_re_eq`).
- `realPositionExponent_slot`: on every slot the two position exponents differ by the weight.

## The admissible modes of the standard vectors

- `slotModes_of_mem`: every `O(r+1)`-finite vector of the standard module `realStandardKFinite (r + 1) ds`
  has `SlotModes` along `slotsOf (blockSlots ds hr) (slotWeight ds)`: by `inClass_slots`, the Fourier
  coefficients along an induced block of weight `k` vanish at the modes that are not
  `±(|k| + 1 + 2l)`.

## The tempered bound on the descending canonical range

- `exists_expand_eq_characterList`: the expansion of a block list of rank `r + 1` is a character
  list `characterList p z` (`isRealCharacterList_expand`, `exists_characterList_of_map_character`).
- `temperedBound_of_mem_range`: let `ds` have rank `r + 1` and imaginary block exponents, and
  `expand ds = characterList p z`. Every function in the range of `canonicalJacquetMap a p z`
  restricted to `realStandardKFinite (r + 1) ds` satisfies, for every `ε > 0`,
  `‖W (torus y · k)‖ ≤ C exp(torusModularLog y / 2 + ε Σ_i |y_i|)` for all `y` and all orthogonal
  `k`. The function is `canonicalJacquetFamily a hφ z` for the profile `φ` of a standard vector of
  `ds`, whose standard section is that vector (`standardSection_compactRestriction`); the
  hypotheses of `canonical_tempered_slot_bound` are `realPositionExponent_slot`,
  `realPositionExponent_re` and `slotModes_of_mem`.
