# Gelfand–Graev representations of general linear groups and product Levis

These are the interface definitions shared by the modules of the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

- `gelfandGraev ψ n` is the compact induction `c-Ind_N^G ψ_N` of the standard character
  `standardCharacter ψ n` of the upper unipotent subgroup `N` of `G = GL_(n+1)(F)`, with right
  translation. Its carrier `GelfandGraevFunctions ψ n` consists of smooth functions `f` with
  `f(u g) = ψ_N(u) f(g)` whose support has compact image in `N \ G`.
- For a block shape `B` of `n`, `leviUpperUnipotent B` is the product of the block upper unipotent
  subgroups inside the product Levi `B.Levi F = ∏ GL_(B.size i)(F)`, and
  `leviWhittakerCharacter B ψ` is the product of the blockwise characters
  `entrywiseCharacter ψ (B.size i)`.
- `leviGelfandGraev B ψ` is the compact induction `c-Ind_{N_M}^M ψ_M` on the product Levi.

The field carries a topological ring structure; groups carry the induced matrix and product
topologies. These are internal definitions (standard objects; Bernstein–Zelevinsky 1976, §5.7
for the mirabolic analogue; Bushnell–Henniart for the Gelfand–Graev representation).
