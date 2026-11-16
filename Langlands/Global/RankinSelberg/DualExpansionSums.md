# Locally uniformly absolutely summable families

Module `Langlands.Global.RankinSelberg.DualExpansionSums`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. Internal infrastructure for the dual expansion.

Provenance: internal; standard facts about series of continuous functions.

- `LocUnifSummable f`: for a family `f : ι → X → ℂ`, the norms are summable at every point and
  the partial sums of the norms converge uniformly on every compact set. This is the form of the
  Whittaker expansion assumed in the Library's `DualCuspidalWhittakerExpansion`.
- `LocUnifSummable.tendstoUniformlyOn`: then the partial sums of the family itself converge
  uniformly on compact sets, and `continuous_tsum` / `continuous_tsum_norm` (for weakly locally
  compact `X`) give continuity of the sums of continuous families.
- `LocUnifSummable.comp`: the property is preserved by composition with a continuous map, and
  `LocUnifSummable.comp_injective` by restriction to an injectively reindexed subfamily
  (using `tsum_subfamily_tail_le`).
