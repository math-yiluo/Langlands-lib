# Closed subgroups: statement target M241.002, the decomposition group is closed

This module states the source unit M241.002 from Naganori Yamaguchi's
*ClassFieldTheory (NYLL)* at commit `fbd320cd8b1b06487c58227e92eb135794267709`: the
theorem `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosed`
in
[`Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean#L55-L81),
lines 55–81, with the theorem at line 57. The declaration
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosedStatement`
in the module `Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.Statements` is
a definition of type `Prop` with universe parameters `u`, `v` and no other parameters. It
proves nothing; a proof of this exact proposition, under the adapted source name, belongs to
a separate proof unit after the statement is published.

## Complete proposition

The imports are the published M239 data module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`
and `Mathlib.FieldTheory.Galois.Infinite`. The module declares `universe u v`. Inside
`namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` (written
as three nested namespace blocks), the entire declaration is:

```lean
def decompositionGroup_isClosedStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (A : _root_.ValuationSubring L),
    IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L))
```

`decompositionGroup` is the published M239.001 abbreviation of the imported module.

## Mathematical meaning

Let `L / K` be an algebraic field extension, not necessarily finite, normal or separable,
and let `A` be a valuation subring of `L`. The group `L ≃ₐ[K] L` of `K`-automorphisms of
`L` carries Mathlib's Krull topology `krullTopology K L` (from
`Mathlib/FieldTheory/KrullTopology.lean`, imported through
`Mathlib.FieldTheory.Galois.Infinite`), in which the subgroups fixing
finite-dimensional intermediate fields form a basis of neighbourhoods of the identity. The
proposition says that the decomposition group of `A`, the set of `σ` with `σ(A) = A`, is
a closed subset of `L ≃ₐ[K] L` in this topology.

## Original-to-adapted map

The whole source file (217 lines) was read. Its SHA-256 is
`17052cbd32890aea579663eeaa851379034027b045bc2fb0daaee402f76ceef3`, the value
recorded for M241 in the
[port inventory](../../../../../notes/reuse/nyll-public-port/m241-m258.md#m241).

| Original lines | Original content | Adapted form |
| --- | --- | --- |
| 1–5 | Copyright and author header | Kept verbatim. A modification note follows it in the same comment. |
| 7 | `import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup` | Replaced by the published M239 data module (Worker 215's artifact `0e135fc0-425a-4406-a36e-f4d889e42935`), which imports `Mathlib.FieldTheory.Galois.Basic` and `Mathlib.RingTheory.Valuation.RamificationGroup`. The statement uses only `decompositionGroup` from the NYLL import chain (`RamificationGroup.lean` imports only `ValuationSubring.lean`). The data module keeps two of the six Mathlib imports of `ValuationSubring.lean`; with line 8 they suffice for this statement. |
| 8 | `import Mathlib.FieldTheory.Galois.Infinite` | Unchanged. |
| 10–17 | Module docstring | Replaced by a docstring for the statement. |
| 19, 27–28, 213–214, 217 | `namespace RamificationTheory`, nested namespaces and their ends | The same namespaces with the prefix `Langlands.NYLL`. |
| 23, 216 | `noncomputable section` … `end` | Omitted. A `Prop` has no computational content. |
| 25 | `universe u v` | Unchanged. |
| 30 | `open scoped Pointwise Topology` | Omitted. The statement uses neither notation. |
| 32 | `variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` | The first binders of the `∀`, same order, names, universes and binder kinds. |
| 33 | `variable [Algebra.IsAlgebraic K L]` | The next binder of the `∀`. It is kept: a theorem includes every instance section variable whose dependencies it includes, and the source theorem has no `omit`. |
| 35–53 | M241.001, the private theorem `mem_decompositionGroup_iff_apply_mem`, with `omit [Algebra.IsAlgebraic K L] in` | Omitted. As a private row of the task, it will be proved inside the proof of this target and recorded in that proof's Markdown. |
| 55–56 | Theorem docstring | Adapted to describe the proposition. |
| 57–59 | `theorem decompositionGroup_isClosed (A : _root_.ValuationSubring L) : IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L))` | The name gets the suffix `Statement`; the binder `A` and the conclusion follow the section binders unchanged. |
| 60–81 | Proof (structure instance with field `isOpen_compl`) | Omitted; later proof unit. |
| 83–211 | Inertia and ramification closedness and the infinite Galois correspondences | Omitted; outside this task. |

### Elaborated telescope

The elaborated type of the source theorem is
`∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
(A : ValuationSubring L), IsClosed ↑(decompositionGroup K A)`, printed with the automatic
universe names `u_1`, `u_2` in place of `u`, `v`. The body of the target is this type.
Hence `K` stays explicit and `L` implicit, and a proof `h` is applied as `h K A`. The
algebraicity hypothesis is exactly where the source has it; no Galois, normality,
separability or finite-dimensionality hypothesis is added, and none is dropped.

## Private fidelity checks

The project Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no errors and no
warnings. Printing the declaration shows a definition of type `Prop` with universe
parameters `u`, `v`. A private draft, not part of this contribution, contained a verbatim
copy of source lines 32–81 (with the M239 abbreviations it needs) in a separate namespace.
It compiled, and Lean accepted:

1. `example : decompositionGroup_isClosedStatement.{u, v} := @source`, so the source proof,
   including the private M241.001 helper, proves the target.
2. `example : decompositionGroup_isClosedStatement.{u, v} = type_of% @source.{u, v} := rfl`.

These checks indicate one proof route. They do not prove the target.

## Reuse search

No equivalent is available by Lean name. Mathlib's
`Mathlib/RingTheory/Valuation/RamificationGroup.lean` defines
`ValuationSubring.decompositionSubgroup` but proves nothing about its topology.
`Mathlib/FieldTheory/Galois/Infinite.lean` gives `ClosedSubgroup` and the infinite Galois
correspondence (`InfiniteGalois.fixingSubgroup_fixedField` and related), whose use needs a
closed subgroup as input. The open fixing subgroups `IntermediateField.fixingSubgroup_isOpen`
used by the source proof are in Mathlib. The Library has no declaration with this name, and
task searches for M241 found no task other than this one.

## Dependencies and consumers

The target depends on the published M239 data module and Mathlib. In the source, M241.002
is used in `ClosedSubgroups.lean` itself, at line 133 of the proof that the inertia group is
closed, and in `ResidueExactSequence.lean` (M243), where
`decompositionGroup_compactSpace` (lines 139–144) derives compactness of the decomposition
group from it. That compactness feeds the maximality instance M243.016.

## Provenance, license and authorship

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the source path above. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The source used
Lean 4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The port
inventory records “none in patch10” for M241, and no compatibility edit was needed. The
Library's `notes/errata` directory has no entry for this source.

The original header is kept verbatim: copyright 2026 Naganori Yamaguchi
([upstream author](https://github.com/n-yamaguchi-0729)), all rights reserved; Apache-2.0;
authors Naganori Yamaguchi (assisted by OpenAI Codex). The existing
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) are unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. NOTICE does not
list `ClosedSubgroups.lean` among its third-party files.

Worker 121 extracted this target, ran the checks above and wrote this companion on
13 November 2026. The Lean header records the modifications.
