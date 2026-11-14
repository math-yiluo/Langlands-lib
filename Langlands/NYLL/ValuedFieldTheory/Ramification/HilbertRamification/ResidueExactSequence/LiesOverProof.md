# NYLL M243.019: the maximal ideal of `A` lies over its contraction to the fixed subring

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver`,
whose type is the published closed target
`selectedMaximalIdeal.instLiesOverStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)), and registers it as a global
instance. It is the proof unit of the source instance M243.019 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem selectedMaximalIdeal.instLiesOver :
    selectedMaximalIdeal.instLiesOverStatement.{u, v}
```

The target is the `abbrev`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (A : _root_.ValuationSubring L),
  (IsLocalRing.maximalIdeal A).LiesOver
    (decompositionFixedMaximalIdeal K A)
```

for an arbitrary field extension `L / K` (no Galois hypothesis) and valuation subring `A`
of `L`. Mathlib's class `Ideal.LiesOver P p` (`Mathlib/RingTheory/Ideal/Over.lean`,
line 125) has the single field `over : p = P.under R`, where `P.under R` is the `abbrev`
`Ideal.comap (algebraMap R B) P` (line 96 of the same file). Here `R` is the fixed subring
`decompositionFixedSubring K A = FixedPoints.subring A (decompositionGroup K A)` (M243.001)
with the algebra structure of a subring over its ambient ring, `B = A`, `P` is the maximal
ideal `𝔪_A` of `A`, and `p` is the published abbreviation (M243.002)
`decompositionFixedMaximalIdeal K A = (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype`.
So the target says: the contraction `𝔪_A ∩ A^D` used throughout M243 is the preimage of
`𝔪_A` under the algebra map `A^D → A`.

## Implemented proof

```lean
intro K L _ _ _ A
constructor
rfl
```

1. `intro` introduces the closed telescope.
2. `constructor` applies the structure constructor of `Ideal.LiesOver`, leaving its field
   `decompositionFixedMaximalIdeal K A = (IsLocalRing.maximalIdeal A).under (decompositionFixedSubring K A)`.
3. Both sides are `Ideal.comap _ (IsLocalRing.maximalIdeal A)`: on the left along
   `(decompositionFixedSubring K A).subtype`, on the right along the algebra map of the
   subring into `A`, which for Mathlib's instance `Algebra.ofSubsemiring`
   (`Mathlib/Algebra/Algebra/Basic.lean`, line 100) is that subtype map by definition
   (`algebraMap_ofSubring`, line 116 of the same file, is proved by `rfl`). So `rfl`
   closes the goal.

The source instance has no private helper, so no private source lemma is used or inlined.

## Instance registration

The theorem is followed by

```lean
attribute [instance] selectedMaximalIdeal.instLiesOver
```

which registers it as a global (not scoped or local) instance under its name in the
namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`, the namespace of the adapted source instance. Because the target is an
`abbrev`, hence reducible, instance registration and instance search see through it to the
class `Ideal.LiesOver`. The module ends with the check

```lean
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver (decompositionFixedMaximalIdeal K A) :=
  inferInstance
```

which compiles; in a development probe `#synth` of this class reported
`selectedMaximalIdeal.instLiesOver K A`. Mathlib's instance `Ideal.over_under`
(`instance over_under : P.LiesOver (P.under A)`, line 128 of `Over.lean`) states the same
fact for the ideal written as `P.under A`, but instance search does not find it for the
target's ideal, which is written as a comap along `Subring.subtype`: in a development probe
without the attribute, `inferInstance` failed for the goal above, also with all of Mathlib
imported. So the new instance is needed and does not duplicate one that applies.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target and, through the published M243 and M239 data modules and their
  Mathlib imports, `Ideal.LiesOver`, `FixedPoints.subring` and the subring algebra
  structure. No other module is imported.

## Source correspondence and modifications

The source instance is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 228–234](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L228-L234):

```lean
/-- Provides the instance `instLiesOver`. -/
instance selectedMaximalIdeal.instLiesOver
    (A : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A) := by
  constructor
  rfl
```

| Source | Adapted |
| --- | --- |
| `instance selectedMaximalIdeal.instLiesOver (A) : (IsLocalRing.maximalIdeal A).LiesOver (decompositionFixedMaximalIdeal K A)` | `theorem selectedMaximalIdeal.instLiesOver : selectedMaximalIdeal.instLiesOverStatement.{u, v}` followed by `attribute [instance] selectedMaximalIdeal.instLiesOver` |
| Tactic proof `constructor; rfl` | `intro`, then the source tactic proof unchanged |
| Docstring “Provides the instance `instLiesOver`.” | Kept |

The following source context is not reproduced: the source imports (replaced by the
imports listed above), `noncomputable section`, and `open scoped Pointwise Topology`
(a `Prop`-valued theorem needs neither the section nor the `Topology` scope). The namespace
`RamificationTheory.HilbertRamification.ValuationSubring` gets the prefix `Langlands.NYLL`,
and `universe u v` is kept. The section variables
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` and the declaration's own
binder `(A : _root_.ValuationSubring L)` are the leading binders of the published closed
target, introduced by `intro`, with the same names, order and binder kinds. The source section variable `[IsGalois K L]` is not in the elaborated type of
this source instance, nor in the target. The `example` above is new and only checks instance
search.

## Development check

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), `lean_check` built this module over the
workspace's Library base `c40a01345b2f4172fa41e07ff31644b40e695003` with no errors and no
warnings. Inspection found a theorem with level parameters `u`, `v` using only the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check is not independent review
or publication.

## Attribution and license

The original copyright and author header (copyright 2026 Naganori Yamaguchi, author
“Naganori Yamaguchi (assisted by OpenAI Codex)”, released under Apache-2.0) is kept
verbatim at the top of the Lean file, followed in the same comment by Worker 173's dated
modification record. The pinned original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, retained in the registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The whole source file
(461 lines) was read; its SHA-256 is
`cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`, as recorded in the
statement Markdown. The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical to the retained
originals, with SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No Mathlib code is copied into this file.
Worker 121's published statement and the imported data modules are used unchanged; all
imported Library modules and their paired Markdown remain frozen.

## Scope

This module proves only M243.019. Besides the theorem and its instance attribute it adds no
declaration. It does not construct the residue field structures M243.020 and M243.021 that
use this instance.
