# Comparison of the level Hecke algebra with the Haar-measure corner

Module `Langlands.Representation.Hecke.LevelHeckeCornerComparisonProof`.
The theorem `Langlands.Hecke.levelHeckeCornerComparison` has exactly the type
`Langlands.Hecke.LevelHeckeCornerComparisonStatement.{u, v}`.
The group universe `u` and representation-space universe `v` are independent.

For every Hausdorff, nonarchimedean, locally compact group with a Borel measurable
structure, every left Haar measure `μ`, and every compact open subgroup `K`,
the theorem supplies a complex linear equivalence

```text
e : LevelHeckeAlgebra ℂ K.toSubgroup ≃ₗ[ℂ] HeckeAlgebra.Corner μ K hK
```

with all three properties of the published target:

1. `e (a * b) = e a * e b`;
2. `e a x = (μ.real (K : Set G) : ℂ)⁻¹ * a.1 (x : G ⧸ K.toSubgroup)`;
3. for every smooth representation `ρ` on a complex module `V : Type v` and
   every `K`-fixed vector `w`, the level action `a • w`, viewed in `V`, is
   `heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (e a)) w`.

No normality, Iwahori decomposition, unimodularity, or additional representation
hypothesis is needed. The representation space is an additive commutative
group with a complex module structure, as in the target.

## Provenance and conventions

This is a derived comparison implementing the published target, using the
normalized coset construction in
[LevelHeckeCornerLinear](LevelHeckeCornerLinear.md). Its relationship with
Renard is explained in the
[target documentation](LevelHeckeCornerComparisonStatement.md).

The source context is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source locations checked by Worker 275 are:

- II.3.11–II.3.12, printed pp.51–53 / PDF pp.57–59: the probability measure
  `e_K`, the identification of Hecke distributions with densities `f μ` for a
  left Haar measure, convolution formula (II.3.12.1), and the unital corner;
- III.1.3 and III.1.5, printed pp.59–60 / PDF pp.65–66: the integrated action
  and the identification of `e_K V` with `V^K`;
- VI.9.4 Proposition, printed p.201 / PDF p.207: the use of unital
  `H(G,K)`-modules in the fixed-vector categorical equivalence.

Renard's Hecke distributions are represented here by their densities for the
chosen measure `μ`. In this function model, `e_K` is the normalized indicator
`μ(K)⁻¹ 1_K`. The level functions are on left cosets `xK`, so their lifts to
`G` are right `K`-invariant. Left Haar measure gives every such coset mass
`μ(K)`. These conventions explain the factor in property 2 and the positive
representative `ρ(x)` in the action formula.

The comparison itself is not a numbered assertion printed in Renard. The
additional subgroup hypotheses in VI.9.4 concern its categorical consequence.
Worker 273 implemented the Lean proof; Worker 275 checked the source context
and conventions.

## Implemented proof

Write `m = (μ.real (K : Set G) : ℂ)`.
The witness is `LevelCorner.linearEquiv μ K hK`, constructed in the helper
module from finite sums of left translates of the normalized indicator:

```text
expansion a = Σ q ∈ a.support, a q • leftTranslate q.out e_K.
```

That module proves the linear bijection and its pointwise formula. In
particular, compact support yields finite quotient support for the inverse
coefficients `q ↦ m * f q.out`, and the nonzero compact-open Haar mass permits
cancellation. These facts supply property 2 and the existence of the witness.

For multiplication, `LevelCorner.cosetTest_mul` uses
`TestFunction.convolution_leftTranslate` to move translation outside
convolution. The published
`HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant` then identifies
`(leftTranslate q.out e_K) * f` with `leftTranslate q.out f` whenever `f` is
left `K`-invariant.

`LevelCorner.toCorner_mul` compares the products after the faithful inclusion
of the corner into the full Hecke algebra. It distributes the finite expansion
of the first factor, applies the preceding translation identity to the second
factor, and evaluates at `x`. The result is

```text
m⁻¹ * Σ q ∈ a.support, a q * b (q.out⁻¹ * x K),
```

which is the level convolution formula `heckeMul_apply`, using
`MulAction.Quotient.smul_mk`. Equality of actual functions gives property 1.

For actions, `LevelCorner.cosetTest_action` uses
`integratedAction_leftTranslate` and
`heckeAction_normalizedIndicator_of_fixed` to show that a normalized coset test
acts on `w` as `ρ q.out w`. Linearity of `heckeAction` gives
`LevelCorner.expansion_action`, the sum `Σ q, a q • ρ q.out w`.
The level action has precisely this sum by `heckeAct_apply`;
`LevelCorner.toCorner_action` identifies the two sides of property 3.

The final theorem instantiates these results at the target's hypotheses and
independent universes, with no additional premise.

## Imports and validation

The proof imports the published target by Lean module name, the linear helper,
and `Langlands.Representation.Hecke.ActionProjection`.
The target and its imported Lean–Markdown pairs are unchanged.
The complete proof and helper compile through the project's Lean service;
declaration inspection reports the universes `u`, `v` and only
`propext`, `Classical.choice`, and `Quot.sound`.
