# Renard VI.2.3–VI.2.4: assembly from the G(F) theorem and VI.2.4

This module reduces the target `UniformAdmissibilityStatements.{u, v}` to two of
its three conjuncts. The `G(F)` conjunct is used in the larger carrier universe
`max u v`. It is a conditional, intermediate result. It proves neither the
uniform admissibility theorem for `G(F)` nor VI.2.4, so it does not prove
`UniformAdmissibilityStatements`.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Theorem VI.2.3 with its Remark and
Proposition VI.2.4 (printed pp.140–142 / PDF pp.146–148). It is registered as
`renard-2026-representations-groupes-reductifs-padiques`. The three published
propositions used here are in
`Langlands/Representation/CuspidalSupport/UniformAdmissibilityStatements.lean`,
and their Markdown gives their correspondence with the source.

## The reduction statement

`UniformAdmissibilityAssemblyReductionStatement.{u, v}` is the implication

```
RationalPointsUniformAdmissibilityStatement.{u, max u v} →
  SupercuspidalUniformCoefficientSupportStatement.{u, v} →
    UniformAdmissibilityStatements.{u, v}
```

Here `u` is the universe of the local field and `v` that of the representation
carriers. The first premise is the VI.2.3 Theorem for `G(F)` with complex smooth
carriers in `Type (max u v)`. The second premise is VI.2.4 at the target
universes. The conclusion is the published conjunction of three statements:
the theorem for `G(F)` with carriers in `Type v`, its analogue for `⁰G` with
carriers in `Type v`, and VI.2.4. Nothing else is assumed or concluded. The
larger carrier universe on the first premise is needed by the `⁰G` step. That
step builds an ambient representation from compact induction, whose carrier is
in `Type (max u v)`.

The reduction is internal content, a composition of published Library
propositions. Its `⁰G` step is the argument of the Remark after VI.2.3
(printed p.141 / PDF p.147). That Remark deduces the `⁰G` result from the
result for `G` as follows. The compact induction from `⁰G` to `G` of an
irreducible `(σ, E)` is of finite type, so it has an irreducible quotient
`(τ, W)`. Frobenius reciprocity for compact induction shows that the restriction
of `τ` to `⁰G` contains `σ`, so `dim E^K ≤ dim W^K ≤ c(G, K)`. The universe
lowering step is a formal consequence of the carrier lift and is not in the
source.

## Proof

`uniformAdmissibilityAssemblyReduction` proves the reduction statement. It
pairs the two theorems below with the VI.2.4 premise.

### Lowering the carrier universe

`rationalPointsUniformAdmissibility_of_max` derives
`RationalPointsUniformAdmissibilityStatement.{u, v}` from the same statement at
`.{u, max u v}`. For `F`, `G`, and a compact open subgroup `K` of `G(F)`, the
premise gives a bound `c`, which is used unchanged. Let `A` be an irreducible
representation with carrier in `Type v`. Its lift `SmoothRep.universeLift.{u} A`
on `ULift A` has carrier in `Type (max u v)`. It is irreducible by
`SmoothRep.isIrreducible_universeLift_iff`, so its `K`-fixed subspace has rank
at most `c`. `Jacquet.fixedVectorsUniverseLiftEquiv` is a linear equivalence
between the `K`-fixed vectors of `A` and those of the lift. By
`LinearEquiv.lift_rank_eq` the two ranks agree after `Cardinal.lift`, and
`Cardinal.lift_le_nat_iff` turns the bound back into `rank A^K ≤ c`.

### The norm kernel

`rationalNormKernelUniformAdmissibility_of_rationalPoints` derives
`RationalNormKernelUniformAdmissibilityStatement.{u, v}` from
`RationalPointsUniformAdmissibilityStatement.{u, max u v}`. Both statements use
the topology `rationalPointTopology F G.X` on `G(F)` and its subspace topology
on `⁰G = Plancherel.rationalCommonNormKernel G`.

Fix `F`, `G`, and a compact open subgroup `K` of `⁰G`. Its image `K'` in `G(F)`
under the subgroup inclusion is
`Plancherel.rationalNormKernelAmbientLevel G K`. This is open because `⁰G` is
open in `G(F)`, and compact by
`Plancherel.isCompact_rationalNormKernelAmbientLevel`. Applying the premise to
`K'` gives a natural number `c`, which is the bound for `K`.

Let `A` be an irreducible smooth complex representation of `⁰G` with carrier in
`Type v`. `Induction.openIrreducibleEmbedding` is applied to the open subgroup
`Plancherel.rationalCommonNormOpenSubgroup G`, whose underlying subgroup is
`⁰G`. It gives an irreducible smooth representation `E` of `G(F)` with carrier
in `Type (max u v)`, and an injective `⁰G`-intertwiner from `A` into the
restriction of `E` to `⁰G`. The published construction takes `E` to be an
irreducible quotient of the compact induction of a carrier lift of `A`. It uses
open Frobenius reciprocity, as in the Remark. By the premise, the `K'`-fixed
subspace of `E` has rank at most `c`.

`Plancherel.fixedVectors_rationalNormKernelAmbientLevel` identifies the
`K`-fixed vectors of the restriction of `E` to `⁰G` with the `K'`-fixed vectors
of `E`. `fixedVectorsMap` restricts the embedding to an injective linear map
from the `K`-fixed vectors of `A` into these fixed vectors.
`LinearMap.lift_rank_le_of_injective` then bounds the lifted rank of `A^K` by
the lifted rank of `E^{K'}`. `Cardinal.lift_le_nat_iff`, used twice, compares
both with `c` and gives `rank A^K ≤ c`.

## Scope

The two theorems are unconditional apart from their stated premises. They use
no admissibility, Bruhat–Tits, Cartan decomposition or Hecke algebra input.
Proving the target still requires a proof of the VI.2.3 Theorem for `G(F)` in
carrier universe `max u v` and a proof of VI.2.4 in universes `u, v`.
