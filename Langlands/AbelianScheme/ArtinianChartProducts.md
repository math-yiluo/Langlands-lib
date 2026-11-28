# Products of models and of chart families

Module `Langlands.AbelianScheme.ArtinianChartProducts` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

- `Model.prod M M'` takes the fibre product `M.Y ⊗ M'.Y` over `Spec R'` and the fibre products
  of the chosen base changes and special fibres. The induced maps are instances of `productMap`
  in `ElementaryReductionProducts`. The lemma `productMap_isPullback` ensures that the two squares
  are again base changes. The lemmas `prod_q_fst`, `prod_q_snd`, `prod_iE_fst`, `prod_iE_snd`
  compute the components.
- `prodV V V'` is the product open `pr₁⁻¹ V ⊓ pr₂⁻¹ V'`, and `VT_prodV` identifies its base change
  with the product of the base changes (`pOpen`, module `ProductOpenCharts`).
- For chart families `K` of `X` and `K'` of `X'` whose residue maps lie over `Spec R`,
  `ChartFamily.prod K K'` is the family of product opens with product charts `prodκ`
  (`prodChart`, module `ProductOpenCharts`), indexed by `K.L × K'.L`. Its transition maps are the
  products of the transition maps (`prod_θS_fst`, `prod_θS_snd`), when `R` is local Artinian.
- For `R` local Artinian and the same residue map compatibility, `Lifts.prod` combines two lifts
  by `θ (l, l') (m, m') = θ l m × θ' l' m'` (`Lifts.prod_θ_fst`, `Lifts.prod_θ_snd`).
