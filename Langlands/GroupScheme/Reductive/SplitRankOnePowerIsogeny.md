# Rank-one isogenies with characteristic-power root maps

This derived supporting module applies to two connected reductive groups over any
field, with supplied `RootCell.IsRootCell` witnesses. The middle commutative group
schemes may differ. Let `t : T ⟶ T'` be an actual isogeny on the middle groups, and
let `q = p^e`, where `ExpChar k p`. The hypotheses on the actual character and
cocharacter maps are `t ≫ χ' = q • χ` and `χv ≫ t = q • χv'`.

`powerHom` chooses the actual group homomorphism constructed by the published
powered-cell gluing argument. `powerHom_spec` retains its commuting torus square,
its negative and positive root restrictions, and its full cell restriction. On
both root coordinates its scheme map is the actual additive-line map `X ↦ X^q`.
The definition itself needs connected reductivity only for the source and does
not need the middle map to be an isogeny.

`powerHom_isIsogeny` additionally assumes connected reductivity of the target
and that `t` is an isogeny. Since the characteristic exponent is nonzero, `q > 0`.
The published power-cell geometry then makes the cell map finite and surjective
on underlying scheme points. Both cell inclusions are open immersions and the
source contains the unit. The generic `OpenCellGeometry.isIsogeny_of_cell`
criterion proves that the ambient map is finite, flat and surjective. In
particular, the conclusion retains the full possibly nonreduced kernel.
`exists_powerIsogeny` packages existence and all four restriction equations.

The provenance is derived from `SplitRankOnePowerCell`,
`SplitRankOnePowerGeometry` and `OpenCellIsogeny`; the proof applies their stated
criteria without new original-literature input. The universe is arbitrary,
characteristic zero (`p = 1`) and `e = 0` are included, and the field need not be
perfect. This module assumes the supplied cells and proves no general-rank graph
construction or general split reductive isogeny theorem.
