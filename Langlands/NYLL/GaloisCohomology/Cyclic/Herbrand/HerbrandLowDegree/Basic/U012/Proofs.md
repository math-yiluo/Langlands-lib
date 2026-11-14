# The Tate norm of the identity (NYLL M113.012)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm_oneStatement.{uG, uA}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm_one.{uG, uA}`. It is the proof phase of M113.012 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
For a finite group `G` acting on a commutative group `A` by multiplicative automorphisms, `N_G 1 = 1`.

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def tateNorm_oneStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A],
    tateNorm G A 1 = 1

theorem tateNorm_one : tateNorm_oneStatement.{uG, uA}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uG, uA` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose six binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `G : Type uG` | Implicit |
| 2 | `A : Type uA` | Implicit |
| 3 | `[Group G]` | Instance-implicit |
| 4 | `[Fintype G]` | Instance-implicit |
| 5 | `[CommGroup A]` | Instance-implicit |
| 6 | `[MulDistribMulAction G A]` | Instance-implicit |

These are exactly the binders of the source theorem after its `omit`: no hypothesis is added or dropped.

`tateNorm G A a` is the published `Basic.Definitions` operator `∏ g : G, g • a` (a product over `Finset.univ` of the `Fintype G`), the finite-group norm `N_G a` of a multiplicative `G`-module.

`MulDistribMulAction G A` is Mathlib's action of a monoid by monoid endomorphisms (`g • (x * y) = g • x * g • y` and `g • 1 = 1`); with `Group G` each `g` acts by an automorphism.

## Implemented proof

The complete theorem is:

```lean
theorem tateNorm_one : tateNorm_oneStatement.{uG, uA} := by
  intro G A _ _ _ _
  unfold tateNorm
  exact Finset.prod_eq_one (fun g _hg => MulDistribMulAction.smul_one g)
```

`intro` introduces all six binders. Then, as in the source, `unfold tateNorm` exposes `∏ g : G, g • (1 : A) = 1`, and `Finset.prod_eq_one` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:108`) closes it because every factor is `1` by the `MulDistribMulAction.smul_one` field (`Mathlib/Algebra/Group/Action/Defs.lean:631`).

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:175–181`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L175-L181)
(partition unit lines 179–185). The source theorem is at line 179, with docstring at line 177 and the `@[simp]` attribute at line 178 (after the `omit` of lines 175–176); its proof is at lines 180–181. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `tateNorm_one`, line 179 | `tateNorm_one : tateNorm_oneStatement.{uG, uA}` |
| Telescope: section variables of lines 62–64 kept by the `omit` of lines 175–176 | Existing closed `tateNorm_oneStatement` |
| Proof, lines 180–181 | Identical, preceded by one `intro` |
| `@[simp]`, line 178 | Dropped (see below) |

Only the first row adds a declaration. Worker 5424's modification (14 November
2026) adds the `Langlands.NYLL` namespace prefix, uses the published closed target
and introduces its binders, and otherwise keeps the source proof. The sole import
is the statement module in place of the source's nine Mathlib imports; the source
`noncomputable section`, section `variable`s, `omit` lines and all other source
declarations are omitted. M113 has no compatibility change in the feasibility
patch10.

The source's `@[simp]` attribute is not reproduced. The published target omits it, and the theorem's type is the closed proposition `tateNorm_oneStatement` rather than an equation, so it could not act as a useful simp lemma. The mathematical content is unchanged.

The retained source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Attribution, licence and environment

The Lean file keeps the original copyright, Apache-2.0 and author header verbatim
(copyright 2026 Naganori Yamaguchi; author "Naganori Yamaguchi (assisted by OpenAI
Codex)"), followed by Worker 5424's dated modification record. Worker 5424
extracted this proof directly from the pinned original and the published statement
module; no worker draft was reused and there are no project coauthors. The
unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already in
the Library and are not modified.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`); upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. In this
environment the module compiles with no errors or warnings and the theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`. Compilation is not
acceptance: publication under `lean.proof@1` also requires the Lake build,
exact-target and unchanged-statement checks, independent semantic review and
integration.

## Scope

This is only the identity value of the norm. The norm homomorphism `tateNormHom` (M113.013, whose `map_one'` field is this result in the source at line 188) and all later units remain separate. These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
