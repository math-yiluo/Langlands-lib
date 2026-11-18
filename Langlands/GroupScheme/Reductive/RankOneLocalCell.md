# Rank-one cell data from local positivity and line facts

This module gives variants of the Library results `RankOneCellData.rankOne_exists_rootGroup`
and `RankOneCellData.rankOne_exists_cell` (in `Reductive/RankOneCellData.lean`). The Library
versions take two published statements as premises:
`RankOnePositiveRootUniquenessStatement` and `SplitRootLieLineStatement`. Here those premises
are replaced by facts about the given group `G` and cocharacter `ν` only. The rank-one
SL2-cover task (Task 7586) may not use `RankOnePositiveRootUniquenessStatement`, so it needs
these local versions.

The setting is a connected reductive group `G` over a field `k`, a split maximal torus
`i : T ⟶ G`, a root `α`, and a cocharacter `ν` with `⟨α, ν⟩ > 0`.

## `RankOneLocalCell.exists_rootGroup`

Hypotheses:

- `hpos`: every root `β` with `⟨β, ν⟩ > 0` equals `α`;
- `hline`: the root space `weightSpace i α` is a line, that is, `k`-linearly equivalent to `k`.

Conclusion: there is a homomorphism `x : 𝔾ₐ ⟶ G` that represents the dynamic unipotent
subgroup `U(ν)`, and `T` acts on it by conjugation through `α`:
`t x(a) t⁻¹ = x(α(t) a)` on all points.

The proof follows the Library proof of `rankOne_exists_rootGroup`. That proof uses its two
premises only through two facts about this one group. First, each chosen polynomial generator
`t_j` of the coordinate ring of `U(ν)` has weight `α`. Second, the `α`-weight space of `T` on
the Lie algebra `Lie(U(ν))` has dimension one. These are statements about the generators and
about the Lie algebra, not about all weights of the coordinate ring. For example, the
generator `t_1` has weight `α`, but the nonzero product `t_1²` has weight `2α`
(`CoordinateWeights.mul_mem_weightSpace`).

- `TorusUnipotence.exists_positiveWeight_coordinates` gives polynomial generators
  `t_1, …, t_d` of the coordinate ring of `U(ν)`, so that the ring is `k[t_1, …, t_d]`. Each
  `t_j` vanishes at the identity and is a `T`-weight vector of some weight `w_j` with
  `⟨w_j, ν⟩ > 0`.
- `TorusUnipotence.exists_triangular_mul` makes the group law triangular in these
  coordinates.
- The generator multiplicity formula `TorusUnipotence.finrank_actionWeightSpace` says the
  following. For every character `χ`, the `χ`-weight space of `T` on `Lie(U(ν))` has
  dimension equal to the number of indices `j` with `w_j = χ`.
- So each `w_j` is a weight of `T` on `Lie(U(ν))`. By
  `Standard.actionWeightSpace_unipotentAction_ne_bot_iff` it is therefore a positive relative
  root: a root with `⟨w_j, ν⟩ > 0`. Then `hpos` gives `w_j = α` for every generator.
- By the multiplicity formula, the `α`-weight space of `Lie(U(ν))` has dimension `d`.
  `Standard.finrank_actionWeightSpace_unipotentAction` is the standard comparison of the Lie
  algebra of the unipotent group with the ambient one. It identifies this dimension with the
  dimension of the ambient root space `weightSpace i α`, which is one by `hline`. So `d = 1`.
- With one coordinate, the triangular group law is additive. `lineCoordinates` and
  `RelativeRoot.vectorGroupIso` then identify `U(ν)` with `𝔾ₐ`, equivariantly for `T`.

## `RankOneLocalCell.exists_oppositeRootGroup`

This is the same result for `-α`, with hypotheses `hneg` (every root negative on `ν` equals
`-α`) and `hline'` (the root space of `-α` is a line). Its proof applies `exists_rootGroup` to
the cocharacter `-ν`, written as `Gm.powerHom (-1) ≫ ν`.

## `RankOneLocalCell.exists_cell`

Hypotheses: `α` and `-α` are roots, `⟨α, ν⟩ > 0`, the torus represents the dynamic centralizer
of `ν` (`hZ`), and `hpos`, `hneg`, `hline`, `hline'` hold.

Conclusion: there are root groups `xp` and `xm` for `α` and `-α`, as above, and the
multiplication `(Y, t, X) ↦ xm(Y) · t · xp(X)` is an open immersion.

The proof combines the two results above with the Library open-cell theorem
`Dynamic.isOpenImmersion_tripleCellMultiplication`.
