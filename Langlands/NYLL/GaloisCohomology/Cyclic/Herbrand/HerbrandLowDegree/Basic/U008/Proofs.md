# Cardinality of `H.subgroupOf K` for `H ≤ K` (NYLL M113.008)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.card_subgroupOf_eq_cardStatement.{uA}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.card_subgroupOf_eq_card.{uA}`. It is the proof phase of M113.008 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
If `H ≤ K` are subgroups of a group `X`, then `H` viewed as a subgroup of `K` (Mathlib's `H.subgroupOf K`, the preimage of `H` under `K.subtype`) has the same `Nat.card` as `H`.

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def card_subgroupOf_eq_cardStatement : Prop :=
  ∀ {X : Type uA} [Group X] [Finite X] {H K : Subgroup X} (hHK : H ≤ K),
    Nat.card (H.subgroupOf K) = Nat.card H

theorem card_subgroupOf_eq_card : card_subgroupOf_eq_cardStatement.{uA}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uA` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose six binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `X : Type uA` | Implicit |
| 2 | `[Group X]` | Instance-implicit |
| 3 | `[Finite X]` | Instance-implicit |
| 4 | `H : Subgroup X` | Implicit |
| 5 | `K : Subgroup X` | Implicit |
| 6 | `hHK : H ≤ K` | Explicit |

These are exactly the binders of the source theorem (whose `omit` removes every section variable): no hypothesis is added or dropped.

## Implemented proof

The complete theorem is:

```lean
theorem card_subgroupOf_eq_card : card_subgroupOf_eq_cardStatement.{uA} := by
  intro X _ _ H K hHK
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
```

`intro` introduces all six binders; the rest is the unchanged source term, used with `exact`. Mathlib's `Subgroup.subgroupOfEquivOfLe hHK : H.subgroupOf K ≃* H` (`Mathlib/Algebra/Group/Subgroup/Map.lean:290`) is a multiplicative equivalence; its underlying equivalence of types gives the equality of cardinalities by `Nat.card_congr` (`Mathlib/SetTheory/Cardinal/Finite.lean:91`).

As in the source, `[Finite X]` is part of the target but not used: the equivalence gives equal `Nat.card` without finiteness.

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:116–124`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L116-L124)
(partition unit lines 121–131). The source theorem is at lines 121–123 (docstring at lines 119–120, after the `omit` of lines 116–118) and its term proof at line 124. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `card_subgroupOf_eq_card`, lines 121–123 | `card_subgroupOf_eq_card : card_subgroupOf_eq_cardStatement.{uA}` |
| Telescope: line 122 (all section variables omitted by lines 116–118) | Existing closed `card_subgroupOf_eq_cardStatement` |
| Term proof, line 124 | Identical term under `exact`, preceded by one `intro` |

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

This is a generic cardinality identity; later units use it separately. These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
