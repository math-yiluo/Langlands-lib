# Equivariant homomorphisms commute with the Tate norm (NYLL M113.010)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.map_tateNormStatement.{uG, uA, uB}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.map_tateNorm.{uG, uA, uB}`. It is the proof phase of M113.010 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
If `f : A →* B` is `G`-equivariant (`f (g • a) = g • f a` for all `g`, `a`), then `f (N_G a) = N_G (f a)` for every `a : A`.

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def map_tateNormStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : A),
    f (tateNorm G A a) = tateNorm G B (f a)

theorem map_tateNorm : map_tateNormStatement.{uG, uA, uB}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uG, uA, uB` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose twelve binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `G : Type uG` | Implicit |
| 2 | `A : Type uA` | Implicit |
| 3 | `B : Type uB` | Implicit |
| 4 | `[Group G]` | Instance-implicit |
| 5 | `[Fintype G]` | Instance-implicit |
| 6 | `[CommGroup A]` | Instance-implicit |
| 7 | `[CommGroup B]` | Instance-implicit |
| 8 | `[MulDistribMulAction G A]` | Instance-implicit |
| 9 | `[MulDistribMulAction G B]` | Instance-implicit |
| 10 | `f : A →* B` | Explicit |
| 11 | `hf : ∀ (g : G) (a : A), f (g • a) = g • f a` | Explicit |
| 12 | `a : A` | Explicit |

These are the source section variables that the theorem uses (the unused `C` variables of lines 62–64 are not included by Lean), followed by its own binders: no hypothesis is added or dropped.

`tateNorm G A a` is the published `Basic.Definitions` operator `∏ g : G, g • a` (a product over `Finset.univ` of the `Fintype G`), the finite-group norm `N_G a` of a multiplicative `G`-module.

`MulDistribMulAction G A` is Mathlib's action of a monoid by monoid endomorphisms (`g • (x * y) = g • x * g • y` and `g • 1 = 1`); with `Group G` each `g` acts by an automorphism.

## Implemented proof

The complete theorem is:

```lean
theorem map_tateNorm : map_tateNormStatement.{uG, uA, uB} := by
  intro G A B _ _ _ _ _ _ f hf a
  simp only [tateNorm, map_prod]
  exact Finset.prod_congr rfl (fun g _hg => hf g a)
```

`intro` introduces all twelve binders; the rest is the unchanged source proof. `simp only [tateNorm, map_prod]` unfolds both norms and pushes `f` through the finite product (Mathlib's `map_prod` for monoid-hom classes, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:366`), leaving `∏ g, f (g • a) = ∏ g, g • f a`; `Finset.prod_congr rfl` with the equivariance `hf g a` closes it termwise.

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:154–159`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L154-L159)
(partition unit lines 155–163). The source theorem is at lines 155–157 (docstring at line 154; no `omit`) and its proof at lines 158–159. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `map_tateNorm`, lines 155–157 | `map_tateNorm : map_tateNormStatement.{uG, uA, uB}` |
| Telescope: used section variables of lines 62–64, then lines 155–156 | Existing closed `map_tateNormStatement` |
| Proof, lines 158–159 | Identical, preceded by one `intro` |

Only the first row adds a declaration. Worker 5424's modification (14 November
2026) adds the `Langlands.NYLL` namespace prefix, uses the published closed target
and introduces its binders, and otherwise keeps the source proof. The sole import
is the statement module in place of the source's nine Mathlib imports; the source
`noncomputable section`, section `variable`s, `omit` lines and all other source
declarations are omitted. M113 has no compatibility change in the feasibility
patch10.

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

This is only the compatibility of the norm with equivariant maps; functoriality of the Herbrand groups is a later, separate unit. These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
