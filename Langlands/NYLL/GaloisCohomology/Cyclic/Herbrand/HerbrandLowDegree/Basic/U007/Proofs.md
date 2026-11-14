# Cardinality at an exact spot of a group-homomorphism sequence (NYLL M113.007)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.monoidHom_card_eq_card_range_mul_card_range_of_exactStatement.{uA, uB, uC}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.monoidHom_card_eq_card_range_mul_card_range_of_exact.{uA, uB, uC}`. It is the proof phase of M113.007 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
If `f : X →* Y` and `g : Y →* Z` satisfy `range f = ker g` and `Y` is finite, then `#Y = #(range f) * #(range g)` (`Nat.card` throughout).

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def monoidHom_card_eq_card_range_mul_card_range_of_exactStatement : Prop :=
  ∀ {X : Type uA} {Y : Type uB} {Z : Type uC} [Group X] [Group Y] [Group Z]
    [Finite Y]
    (f : X →* Y) (g : Y →* Z)
    (hexact : MonoidHom.range f = MonoidHom.ker g),
    Nat.card Y = Nat.card (MonoidHom.range f) * Nat.card (MonoidHom.range g)

theorem monoidHom_card_eq_card_range_mul_card_range_of_exact : monoidHom_card_eq_card_range_mul_card_range_of_exactStatement.{uA, uB, uC}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uA, uB, uC` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose ten binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `X : Type uA` | Implicit |
| 2 | `Y : Type uB` | Implicit |
| 3 | `Z : Type uC` | Implicit |
| 4 | `[Group X]` | Instance-implicit |
| 5 | `[Group Y]` | Instance-implicit |
| 6 | `[Group Z]` | Instance-implicit |
| 7 | `[Finite Y]` | Instance-implicit |
| 8 | `f : X →* Y` | Explicit |
| 9 | `g : Y →* Z` | Explicit |
| 10 | `hexact : MonoidHom.range f = MonoidHom.ker g` | Explicit |

`X` and `Z` need not be finite. These are exactly the binders of the source theorem (whose `omit` removes every section variable): no hypothesis is added or dropped.

## Implemented proof

The complete theorem is:

```lean
theorem monoidHom_card_eq_card_range_mul_card_range_of_exact :
    monoidHom_card_eq_card_range_mul_card_range_of_exactStatement.{uA, uB, uC} := by
  intro X Y Z _ _ _ _ f g hexact
  -- Inlined source proof of M113.006 for `g`: `#Y = #ker g * #range g`.
  rw [← (MonoidHom.ker g).card_mul_index, Subgroup.index_ker, ← hexact]
```

`intro` introduces all ten binders. The source proof (line 114) is `rw [monoidHom_card_eq_card_ker_mul_card_range g, ← hexact]`, i.e. it uses M113.006 for `g`. M113.006 is a separate candidate of this task and is not yet in the Library, so, as the task permits, its own two rewrites (source lines 99–100) are inlined in the same `rw` instead of adding a local copy of the lemma:

1. `← (MonoidHom.ker g).card_mul_index` (Mathlib `Subgroup.card_mul_index`, `Mathlib/GroupTheory/Index.lean:290`) turns `Nat.card Y` into `Nat.card (ker g) * (ker g).index`;
2. `Subgroup.index_ker` (`Mathlib/GroupTheory/Index.lean:282`) turns the index into `Nat.card (range g)` — together steps 1–2 are exactly M113.006 for `g`;
3. `← hexact` replaces `ker g` by `range f`, and the goal `Nat.card (range f) * Nat.card (range g) = …` closes by reflexivity.

As in the source, `[Finite Y]` is part of the target but not used by these rewrites, which hold with Mathlib's `Nat.card`/`index` conventions.

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:99–114`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L99-L114)
(partition unit lines 108–120). The source theorem is at lines 108–113 (docstring at lines 105–107, after the `omit` of lines 102–104) and its proof at line 114; the inlined M113.006 rewrites are at lines 99–100. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `monoidHom_card_eq_card_range_mul_card_range_of_exact`, lines 108–113 | `monoidHom_card_eq_card_range_mul_card_range_of_exact : monoidHom_card_eq_card_range_mul_card_range_of_exactStatement.{uA, uB, uC}` |
| Telescope: lines 109–112 (all section variables omitted by lines 102–104) | Existing closed `monoidHom_card_eq_card_range_mul_card_range_of_exactStatement` |
| Proof, line 114 (`rw` with M113.006 for `g`, then `← hexact`) | `intro`, then one `rw` with the two M113.006 rewrites of lines 99–100 for `g`, then `← hexact` |

Only the first row adds a declaration. Worker 5424's modification (14 November
2026) adds the `Langlands.NYLL` namespace prefix, uses the published closed target
and introduces its binders, and otherwise keeps the source proof. The sole import
is the statement module in place of the source's nine Mathlib imports; the source
`noncomputable section`, section `variable`s, `omit` lines and all other source
declarations are omitted. M113 has no compatibility change in the feasibility
patch10.

The only deviation from the source proof is the inlining of M113.006 described above; no declaration named `monoidHom_card_eq_card_ker_mul_card_range` (or any other) is added here, so this module does not conflict with the separate M113.006 proof.

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

This is a generic cardinality identity for one exact spot; the Herbrand-quotient applications are later, separate units. These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
