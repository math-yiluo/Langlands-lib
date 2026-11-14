# NYLL M243.014: the fixed subring is the invariant ring of the decomposition group

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsInvariant`,
whose type is the published closed target
`decompositionFixedSubring.instIsInvariantStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)), and registers it as a global
instance. It is the proof unit of the source instance M243.014 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem decompositionFixedSubring.instIsInvariant :
    decompositionFixedSubring.instIsInvariantStatement.{u, v}
```

The target is the `abbrev`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (A : _root_.ValuationSubring L),
  Algebra.IsInvariant (decompositionFixedSubring K A) A
    (decompositionGroup K A)
```

for an arbitrary field extension `L / K` (no Galois hypothesis) and valuation subring `A`
of `L`. Mathlib's class `Algebra.IsInvariant R B G` (`Mathlib/RingTheory/Invariant/Defs.lean`,
line 31) has the single field
`isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : R, algebraMap R B a = b`. Here
`R` is the fixed subring `decompositionFixedSubring K A = FixedPoints.subring A (decompositionGroup K A)`
(M243.001) with the algebra structure of a subring over its ambient ring, `B = A`, and `G`
is the decomposition group acting through Mathlib's
`ValuationSubring.decompositionSubgroupMulSemiringAction`
(`Mathlib/RingTheory/Valuation/RamificationGroup.lean`, line 40). So the target says: every
element of `A` fixed by every element of the decomposition group is the image of an element
of the fixed subring.

## Implemented proof

```lean
intro K L _ _ _ A
constructor
intro x hx
exact ⟨⟨x, hx⟩, rfl⟩
```

1. `intro` introduces the closed telescope.
2. `constructor` applies the structure constructor of `Algebra.IsInvariant`, leaving its
   field `∀ b : A, (∀ g, g • b = b) → ∃ a, algebraMap _ A a = b`.
3. For `x : A` and `hx : ∀ g, g • x = x`, the hypothesis `hx` is by definition the
   membership `x ∈ FixedPoints.subring A (decompositionGroup K A)` (the carrier of
   `FixedPoints.subring` is that of `FixedPoints.submonoid`, whose membership is
   `∀ m, m • x = x`), so `⟨x, hx⟩` is an element of the fixed subring. Its image under the
   algebra map of the subring into `A` is its underlying element `x`, definitionally, so
   `rfl` proves `algebraMap _ A ⟨x, hx⟩ = x`.

## Private source helper M243.012, inlined

The source instance applies the private theorem M243.012
`decompositionFixedSubring_isInvariant`, [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 156–163](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L156-L163):

```lean
omit [IsGalois K L] in
private theorem decompositionFixedSubring_isInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) := by
  constructor
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩
```

Its conclusion and telescope are exactly those of the target. Its three-line tactic proof is
inlined unchanged as steps 2–3 above, after the `intro` of step 1, so this theorem
establishes the content of M243.012 inside the proof that consumes it, as Task 5836 allows
for private rows. No separate declaration for M243.012 is introduced. The source also uses
M243.012 inside the private theorem M243.015 and in the proofs of M243.029 and M243.030
(lines 372 and 409); there the instance registered here supplies the same proposition. No
other private source lemma is used.

## Instance registration

The theorem is followed by

```lean
attribute [instance] decompositionFixedSubring.instIsInvariant
```

which registers it as a global (not scoped or local) instance under its name in the
namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`, the namespace of the adapted source instance. Because the target is an
`abbrev`, hence reducible, instance registration and instance search see through it to the
class `Algebra.IsInvariant`; the arguments `K`, `L`, `A` and the field and algebra
instances are determined by the goal. The module ends with the check

```lean
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A (decompositionGroup K A) :=
  inferInstance
```

which compiles; in a development probe `#synth` of this class reported
`decompositionFixedSubring.instIsInvariant K A`. Mathlib has no `Algebra.IsInvariant`
instance for `FixedPoints.subring` (a search of `Mathlib/` for one found none, as the
statement Markdown also records), so the new instance does not duplicate or conflict with a
Mathlib instance.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target and, through the published M243 and M239 data modules and their
  Mathlib imports, `Algebra.IsInvariant`, `FixedPoints.subring` and the action above. No other
  module is imported.

## Source correspondence and modifications

The source instance is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 172–177](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L172-L177):

```lean
/-- Provides the instance `instIsInvariant`. -/
instance decompositionFixedSubring.instIsInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
  decompositionFixedSubring_isInvariant (K := K) A
```

| Source | Adapted |
| --- | --- |
| `instance decompositionFixedSubring.instIsInvariant (A) : Algebra.IsInvariant (decompositionFixedSubring K A) A (decompositionGroup K A)` | `theorem decompositionFixedSubring.instIsInvariant : decompositionFixedSubring.instIsInvariantStatement.{u, v}` followed by `attribute [instance] decompositionFixedSubring.instIsInvariant` |
| Proof `decompositionFixedSubring_isInvariant (K := K) A` (M243.012) | `intro`, then M243.012's tactic proof unchanged |
| Docstring “Provides the instance `instIsInvariant`.” | Kept |

The following source context is not reproduced: the source imports (replaced by the
imports listed above), `noncomputable section`, and `open scoped Pointwise Topology`
(a `Prop`-valued theorem needs neither the section nor the `Topology` scope). The namespace
`RamificationTheory.HilbertRamification.ValuationSubring` gets the prefix `Langlands.NYLL`,
and `universe u v` is kept. The section variables
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` and the declaration's own
binder `(A : _root_.ValuationSubring L)` are the leading binders of the published closed
target, introduced by `intro`, with the same names, order and binder kinds. The source section variable `[IsGalois K L]` is not in the elaborated type of
this source instance (its helper is declared with `omit [IsGalois K L] in`), nor in the
target. The `example` above is new and only checks instance search.

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

This module proves only M243.014 (and, inlined, the private M243.012). Besides the theorem
and its instance attribute it adds no declaration.
