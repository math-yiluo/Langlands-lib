# Unions and conjugates of chart families

Module `Langlands.AbelianScheme.ArtinianChartOperations` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

The constructions apply to chart families of a model `M` of a scheme `X` (module
`ArtinianChartFamily`). Statements about transition maps and lifts assume `R` local Artinian.
`Lifts.sum` and `sumLift₂` also assume `R'` Artinian and `M.Y` separated and smooth over `Spec R'`.

## Unions

`ChartFamily.sum K₁ K₂` is the family indexed by `K₁.L ⊕ K₂.L`. Its transition maps on each
summand are those of `K₁` and `K₂` (`sum_θS_inl`, `sum_θS_inr`). `Lifts.sum D₁ D₂` combines lifts on
the two families, using `D₁` and `D₂` on the diagonal blocks (`Lifts.sum_θ_inl`, `Lifts.sum_θ_inr`)
and chosen lifts (`sumLift₂`, from `exists_lift₂`) across the two families.

## Conjugates

`Model.Aut` consists of compatible automorphisms `αY` of `Y` over `Spec R'`, `αS` of its base
change over `Spec R`, `αE` of its special fibre and `αX` of `X` over `Spec R`. The map `αS`
covers `αY`, `αE` covers `αS`, and `e` intertwines `αE` and `αX`. For such `a`, the conjugated
family `K.conj a` has the opens `αY⁻¹(V l)` and the
charts `αX⁻¹ ∘ κ l ∘ αS`. Its transition maps are the conjugates of those of `K` (`conj_lift`,
`conj_θS`, `conj_θS_q`), and `Lifts.conj` conjugates the lifts by the formula
`θ' l m = αY⁻¹ ∘ θ l m ∘ αY` on the double overlaps (`Lifts.conj_θ`).

These operations are used to build charts of the square of an abelian scheme out of product charts
and their shears (module `ArtinianSquareCharts`).
