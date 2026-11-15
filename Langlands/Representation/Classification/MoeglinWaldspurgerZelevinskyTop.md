# The derivative of a Zelevinsky label at the top point

Module `Langlands.Representation.Classification.MoeglinWaldspurgerZelevinskyTop`. Written by
Worker 5735 for Task 5735.

`zmax_LDrel` (field `zmax` of `DerivativeFacts` for `LDrel`): assuming
`LeftCuspidalDerivativeLemma`, if every occurrence of `β` ends at most at `y`, `cls` is the label
of `β` and `S` the label of `β' = β - j·[y, y]` (`j` the number of point occurrences `[y, y]`),
then `LDrel y cls j S`.

Proof. Take an irreducible `D₀` of class `S` embedded in a precedence-ordered product `d₀` of
segment socles for `realize β'`. The datum `iterCons y j d₀` (with `j` point blocks first) has
multisegment `realize β`, is precedence ordered (a point `[y, y]` precedes no realized interval
ending at most at `y`, by `realize_precedes_iff`) and consists of socles. An irreducible
subrepresentation `π` of `A^j × D₀` (nonzero, finite length) embeds into its product, so it is a
label of `β` and has class `cls` (`labelClass_unique`, from the published `isLabel_unique`).
`D₀` is left reduced: the blocks of `d₀` are socles of segments not beginning at `y`
(`socle_leftReduced`, the segment clause), `datum_leftReduced` gives the product, and the
subquotient clause passes to `D₀`. Then `π ↪ A^j × D₀` is the required datum (no comparison
clause is needed). Helpers: `point_length`, `weight_replicate_point`, `labelClass_unique`,
`mem_realize`, `socle_leftReduced`.
