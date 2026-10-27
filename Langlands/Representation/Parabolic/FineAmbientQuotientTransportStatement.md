# Fine-to-ambient quotient transport

`Langlands.FineAmbientQuotientTransportStatement.{uF,uV,uW,uZ}` is an internal
algebraic transport target for the actual normalized induction constructions.
This file defines the proposition and supplies no proof.

## Statement

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p`, topological data `T`
for `F`, any rank `n` (zero is allowed), an ordered block shape `B` of `n`,
and a refinement `S` of `B`. The fine input `ω` is a representation of the
actual product Levi of the flattened shape `B.flatten S`, smooth for the Levi
topology induced by `T`. The field, fine input `ω`, coarse input `π` and
ambient target `J` live in the independent universes `uF`, `uV`, `uW` and
`uZ`.

Let `v₀` be any real parameter on the blocks of `B.flatten S` and `t` any
real parameter on the blocks of `B`. For every coarse representation `π` of
`B.Levi`, every `J` of `GL_n(F)`, and every pair of individually given actual
surjective intertwiners

1. `q₀` from `innerInduced T B S (fineTwist T B S ω v₀ 0)` onto `π`, and
2. `q` from `CuspidalJacquetMultiplicity.induced T B` of the coarse real twist
   `T.leviRealPowerTwist B t π.ρ` onto `J`,

the proposition asserts that there is an actual surjective intertwiner from
`RelativeRecovery.fineAmbientInduced T B S ω v₀ t` onto the same `J`.
That ambient induction twists `ω` on the flattened block `k` by the exact
exponent `-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`, so each fine block
carries the coarse parameter of the coarse block containing it.

All inducing groups, flattened coordinates, character twists and maps are the
existing Library constructions. The outer inductions induce from the upper
block parabolic of `GL_n(F)`; the inner induction induces inside `B.Levi` from
the product of the upper block parabolics of the refinements `S i`, and
`fineTwist` reaches its refined Levi through the actual flattened Levi
equivalence. Each normalized induction is smooth induction by right
translation, with covariance by the positive half of the modulus. Real twists
use the absolute value of each block determinant normalized by the
residue-field cardinality.

The only representation regularity hypothesis is smoothness of `ω`. There is
no irreducibility, admissibility, cuspidality, unitarity or temperedness
condition, no positive-rank condition, and no positivity, chamber or
`StrictAnti` condition on `v₀` or `t`. Smoothness of `π` is not a premise:
`π` is the image of `q₀`, whose source is a normalized refined induction and
hence smooth. The statement selects no head or Langlands quotient.

## Provenance

This is a derived internal statement, not a transcription of a theorem in the
original literature. It isolates the algebraic step that moves a specified
quotient of the coarse outer induction to the fine ambient induction used in
`Langlands.GLTemperedRelativeQuotientReflectionStatement`; it asserts neither
that reflection nor supported recovery, and it is distinct from nested
induction inside a product Levi.

The intended proof composes existing Library results. The published
`Langlands.refinedLeviRealTwist` turns `q₀` into a surjection from the inner
induction of `fineTwist T B S ω v₀ t` onto `T.leviRealPowerTwist B t π.ρ`.
Normalized parabolic induction preserves smooth surjections by
`Langlands.Parabolic.normalizedInducedSurjectivity_of_smoothInductionSurjectivity`
with `Langlands.Induction.smoothInductionSurjectivity`; smoothness of `π`
comes from `Langlands.isSmooth_of_surjective` and
`T.isSmooth_normalizedRefinedInduced`, and real twists keep smoothness by
`T.isSmooth_leviRealPowerTwist_iff`. Composing with `q` and the inverse of
ordered induction in stages, `Langlands.Parabolic.orderedRefinementInductionEquiv`
at the canonical coordinates `B.flattenBlockEquiv S`, gives the conclusion.
That equivalence needs a smooth input, which smoothness of `ω` supplies.
The coordinate identification is
`Langlands.GeneralLinear.BlockShape.leviRefinementEquiv_flatten` in
`Langlands.Representation.Parabolic.ComposedFlattenedInductionProof`; no
arbitrary Levi equivalence is an input. This route is planning information
only: no proof of this proposition is published.
