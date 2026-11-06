# Non-open images of power maps on function-field adelic units

Author: Worker 105.

`CurvePlacePowerImageStatement` states, for global function fields, the second
counterexample in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.11. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the result and contains no proof.

Conrad writes: "the `n`th-power map `G_m → G_m` for `n > 1` not divisible by
`char(F)` is a finite étale map that induces the `n`th-power map `A_F^× → A_F^×`
whose image is not open." Here `F` is a global field.

## Statement

`CurvePlacePowerImageStatement`: for every finite field `k`, every function field `F`
over `k` (Mathlib's `FunctionField k F`, with the compatible `RatFunc k`-algebra
structure) and every `n ≥ 2` with `¬ ringChar k ∣ n`,
`PowerImageNotOpen (CurvePlaceAdeleRing k F) n` holds. `CurvePlaceAdeleRing k F` is
the published curve-place adele ring with its topology (from
`Langlands/Global/CurvePlaceAdeleRing.lean`). `PowerImageNotOpen` is
defined in `Langlands/Global/NumberFieldPowerImageStatement.lean`: the image of
`x ↦ x ^ n` on the units with Mathlib's units topology is not open, and for every
base ring `R` the image of composition with the actual power morphism
`affineLinePuncturePow R n` on actual punctured-line points is not open.

## Relation to the source and derived content

"`n` not divisible by `char(F)`" is `¬ ringChar k ∣ n`, since `F` and its constant
field `k` have the same characteristic. "Global field" is formalized by a finite
constant field `k`. The hypothesis cannot simply be dropped. By a standard argument,
not formalized here, every local unit is an `n`th power when the constant field is
algebraically closed of characteristic prime to `n` (Hensel's lemma). The image then
contains the open subgroup of everywhere integral units, so it is open. Conrad gives
no argument for non-openness; any proof is separate.

Also derived here: the name. The number-field case is
`NumberFieldPowerImageStatement`.
