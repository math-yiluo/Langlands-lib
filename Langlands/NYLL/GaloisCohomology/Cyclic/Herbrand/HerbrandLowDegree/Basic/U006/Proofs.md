# Cardinality of the source of a group homomorphism (NYLL M113.006)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.monoidHom_card_eq_card_ker_mul_card_rangeStatement.{uA, uB}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.monoidHom_card_eq_card_ker_mul_card_range.{uA, uB}`. It is the proof phase of M113.006 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
For a group homomorphism `f : X →* Y` with `X` finite, `#X = #(ker f) * #(range f)` (`Nat.card` throughout); this is the cardinality form of the first isomorphism theorem.

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def monoidHom_card_eq_card_ker_mul_card_rangeStatement : Prop :=
  ∀ {X : Type uA} {Y : Type uB} [Group X] [Group Y] [Finite X] (f : X →* Y),
    Nat.card X = Nat.card (MonoidHom.ker f) * Nat.card (MonoidHom.range f)

theorem monoidHom_card_eq_card_ker_mul_card_range : monoidHom_card_eq_card_ker_mul_card_rangeStatement.{uA, uB}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uA, uB` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose six binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `X : Type uA` | Implicit |
| 2 | `Y : Type uB` | Implicit |
| 3 | `[Group X]` | Instance-implicit |
| 4 | `[Group Y]` | Instance-implicit |
| 5 | `[Finite X]` | Instance-implicit |
| 6 | `f : X →* Y` | Explicit |

`Y` need not be finite. These are exactly the binders of the source theorem (whose `omit` removes every section variable): no hypothesis is added or dropped. Note that the universe names follow the source, which reuses its `uA uB` universes for `X` and `Y`.

## Implemented proof

The complete theorem is:

```lean
theorem monoidHom_card_eq_card_ker_mul_card_range :
    monoidHom_card_eq_card_ker_mul_card_rangeStatement.{uA, uB} := by
  intro X Y _ _ _ f
  rw [← (MonoidHom.ker f).card_mul_index,
    Subgroup.index_ker]
```

`intro` introduces all six binders; the rest is the unchanged source rewrite.

1. `rw [← (MonoidHom.ker f).card_mul_index]` rewrites `Nat.card X` with Mathlib's `Subgroup.card_mul_index` (`Nat.card H * H.index = Nat.card G`, `Mathlib/GroupTheory/Index.lean:290`) read right to left, giving `Nat.card (ker f) * (ker f).index`.
2. `Subgroup.index_ker` (`f.ker.index = Nat.card f.range`, `Mathlib/GroupTheory/Index.lean:282`) replaces the index, and the goal closes by reflexivity inside `rw`.

Neither Mathlib lemma needs `[Finite X]`: `Nat.card` and `Subgroup.index` use the convention that infinite cardinalities and indices are `0`. The finiteness hypothesis is part of the target but unused by this proof (as in the source).

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:90–100`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L90-L100)
(partition unit lines 96–107). The source theorem is at lines 96–98 (docstring at lines 93–95, after the `omit` of lines 90–92) and its proof at lines 99–100. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `monoidHom_card_eq_card_ker_mul_card_range`, lines 96–98 | `monoidHom_card_eq_card_ker_mul_card_range : monoidHom_card_eq_card_ker_mul_card_rangeStatement.{uA, uB}` |
| Telescope: lines 97 (all section variables omitted by lines 90–92) | Existing closed `monoidHom_card_eq_card_ker_mul_card_rangeStatement` |
| `rw` proof, lines 99–100 | Identical, preceded by one `intro` |

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

This is a generic cardinality identity. The exact-sequence corollary M113.007 is a separate candidate (it inlines this rewrite rather than importing this module). These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
