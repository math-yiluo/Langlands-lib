# Splitting minuscule coset representatives along two blocks

Module `Langlands.Representation.Shahidi.OpenCellHeckeSplit`, namespace
`Langlands.Shahidi.OpenCell`.

A subset `S ⊆ Fin (m + n)` is the pair of its parts `S₁ ⊆ Fin m` and `S₂ ⊆ Fin n`
(`firstPart`, `secondPart`, `joinParts`, `splitEquiv`). The module counts the radical pairs
`(i, j)`, `i ∈ S`, `j ∉ S`, `i < j`, along the two blocks: `card_radicalPairs_split` gives
`#RP(S) = #RP(S₁) + #RP(S₂) + |S₁| (n - |S₂|)`; sums over subsets split accordingly
(`sum_card_eq_split`, `prod_mem_split`).

## Provenance

Elementary combinatorics for the minuscule Hecke operators of the Library
(`Unramified.MinusculeCosets`).
