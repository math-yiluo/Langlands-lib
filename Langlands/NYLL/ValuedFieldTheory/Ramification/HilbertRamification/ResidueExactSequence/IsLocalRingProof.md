# NYLL M243.007: the fixed subring of the decomposition group is local

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing`,
whose type is the published closed target
`decompositionFixedSubring.instIsLocalRingStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)). It is the proof unit of the source
instance M243.007 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem decompositionFixedSubring.instIsLocalRing :
    decompositionFixedSubring.instIsLocalRingStatement.{u, v}
```

The target is the `abbrev`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (A : _root_.ValuationSubring L),
  IsLocalRing (decompositionFixedSubring K A)
```

for an arbitrary field extension `L / K` (no Galois hypothesis) and valuation subring `A`
of `L`. Here `decompositionFixedSubring K A` is the published abbreviation (M243.001) for
`FixedPoints.subring A (decompositionGroup K A)`, the subring of `A` fixed by the
decomposition group `decompositionGroup K A = A.decompositionSubgroup K` (M239.001), acting
on `A` through Mathlib's `ValuationSubring.decompositionSubgroupMulSemiringAction`
(`Mathlib/RingTheory/Valuation/RamificationGroup.lean`, line 40).

## Implemented proof

```lean
intro K L _ _ _ A
exact FixedPoints.isLocalRing_subring
```

After the closed telescope is introduced, the goal `IsLocalRing (decompositionFixedSubring K A)`
is, by unfolding the `abbrev`, `IsLocalRing (FixedPoints.subring A (decompositionGroup K A))`.
This is the conclusion of the published Library instance

```lean
instance FixedPoints.isLocalRing_subring {R : Type*} [Ring R] {M : Type*} [Monoid M]
    [MulSemiringAction M R] [IsLocalRing R] : IsLocalRing (FixedPoints.subring R M)
```

(`Langlands/AnthropicFLT/Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean`,
line 50) at `R := A` and `M := decompositionGroup K A`. Its instance arguments are found by
instance search: the ring structure of `A`, Mathlib's `ValuationSubring.isLocalRing`
(`Mathlib/RingTheory/Valuation/ValuationSubring.lean`, line 148) and the action named above.
The Library instance's own proof uses `FixedPoints.isUnit_subring_iff` (line 34 of the same
file): an element of the fixed subring is a unit there exactly when it is a unit of `R`,
because the inverse of a fixed unit is fixed. If `a + b = 1` in the fixed subring, then
`a + b = 1` in the local ring `R`, so `a` or `b` is a unit of `R` and hence of the fixed
subring.

## Instance registration

As the task requires, the theorem is **not** registered as an instance. The existing global
instance `FixedPoints.isLocalRing_subring` already supplies
`IsLocalRing (decompositionFixedSubring K A)` to instance search wherever its module is
imported (this module imports it), so registering the theorem would only add a second global
instance for the same goals. The module ends with the check

```lean
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  inferInstance
```

which compiles. In a development probe, `#synth IsLocalRing (decompositionFixedSubring K A)`
reported `FixedPoints.isLocalRing_subring`. Consumers that need the source instance, such as
the published M243.017 target in `MaximalIdealStatement.lean`, obtain it from that instance.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target, and through it the published M243 and M239 data modules.
- `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`:
  the instance `FixedPoints.isLocalRing_subring` (this published module imports all of
  Mathlib).

The source instance has no private helper, so no private source lemma is used or inlined.

## Source correspondence and modifications

The source is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 96–100](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L96-L100):

```lean
/-- Provides the instance `instIsLocalRing`. -/
instance decompositionFixedSubring.instIsLocalRing
    (A : _root_.ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  (decompositionFieldValuationSubringEquivFixedSubring (K := K) A).isLocalRing
```

The source transports the local-ring structure of the valuation subring `A ∩ Z_w` of the
decomposition field along the ring equivalence M243.006
`decompositionFieldValuationSubringEquivFixedSubring` (published in the Definitions module),
using Mathlib's `RingEquiv.isLocalRing`. As the task directs, this proof uses instead the
Library's general fixed-subring instance, which proves the same proposition; the route through
M243.006 is not needed.

| Source | Adapted |
| --- | --- |
| `instance decompositionFixedSubring.instIsLocalRing (A) : IsLocalRing (decompositionFixedSubring K A)` | `theorem decompositionFixedSubring.instIsLocalRing : decompositionFixedSubring.instIsLocalRingStatement.{u, v}` |
| `instance` keyword | Not kept, and no `attribute [instance]` (see above) |
| Proof `(decompositionFieldValuationSubringEquivFixedSubring (K := K) A).isLocalRing` | `intro`, then `FixedPoints.isLocalRing_subring` |
| Docstring “Provides the instance `instIsLocalRing`.” | Rewritten to say which existing instance supplies it |

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
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The Library instance used here comes from the Anthropic FLT port (Apache-2.0), credited in its own module; none of its code is copied here.
Worker 121's published statement and the imported data modules are used unchanged; all
imported Library modules and their paired Markdown remain frozen.

## Scope

This module proves only M243.007, the locality of the fixed subring. It adds no global
instance and no other declaration. It does not prove that the contracted ideal is the maximal
ideal (M243.017) or any other row of M243.
