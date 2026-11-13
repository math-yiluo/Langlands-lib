# Field range of the compatible lower embedding: statement target

`Langlands.NYLL.PortInternal.M262.d006Statement` is the proposition that, in a
tower `K ⊆ E ⊆ L` with a `K`-embedding `iL : L →ₐ[K] SeparableClosure K`, the
image of `E` under the restricted embedding lies inside the image of `L`. In
Lean:

```lean
def d006Statement
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) : Prop :=
  AlgHom.fieldRange (d004 K E L iL) ≤
    AlgHom.fieldRange iL
```

This is the statement of source unit M262.006, a private helper lemma. Defining
the proposition does not prove it.

## Parameters and meaning

All three fields lie in `Type 0`, as in the source, and the declaration has no
universe parameters. The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K`, `E`, `L` | explicit, `Type` | Base, middle and upper field |
| `[Field K]`, `[Field E]`, `[Field L]` | instance-implicit | Field structures |
| `[Algebra K E]`, `[Algebra E L]`, `[Algebra K L]` | instance-implicit | The three algebra structures of the tower |
| `[IsScalarTower K E L]` | instance-implicit | Compatibility of the three algebra maps |
| `iL : L →ₐ[K] SeparableClosure K` | explicit | Supplied embedding of the upper field |

The statement uses these definitions:

- `d004 K E L iL` is the published
  `Langlands.NYLL.PortInternal.M262.d004`, defined as
  `iL.comp (IsScalarTower.toAlgHom K E L)`. It is the `K`-embedding of `E`
  sending `x` to `iL (algebraMap E L x)`.
- `AlgHom.fieldRange f` is Mathlib's image of a `K`-algebra homomorphism of
  fields, as an `IntermediateField K (SeparableClosure K)`. It is defined in
  `Mathlib/FieldTheory/IntermediateField/Basic.lean`, line 540.
- `≤` is the order on intermediate fields of `SeparableClosure K / K`, which is
  inclusion of the underlying sets.

`SeparableClosure K` is Mathlib's abbreviation
`separableClosure K (AlgebraicClosure K)` (`Mathlib/FieldTheory/IsSepClosed.lean`,
line 349). The statement assumes no finite-dimensionality, normality, Galois,
valuation, topology or local-field hypothesis.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`.
The private theorem's statement is at lines 66–73 and its proof at 74–76. The
file's SHA-256 is
`a81fa466df15d0d72f24428f0780a68b9a9f434fa4d27746beafe71bfae521c0`. The source
statement reads:

```lean
private theorem towerEmbeddedFieldRange_le
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    AlgHom.fieldRange (towerLowerEmbedding K E L iL) ≤
      AlgHom.fieldRange iL := by
```

The source file declares no `variable` before this theorem, so the theorem's
binders are its whole telescope. The private source definition
`towerLowerEmbedding` (lines 44–51) is published as
`Langlands.NYLL.PortInternal.M262.d004`, with the same telescope and body.

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| Private `LocalClassFieldTheory.towerEmbeddedFieldRange_le` (M262.006) | `Langlands.NYLL.PortInternal.M262.d006Statement` |
| Private `LocalClassFieldTheory.towerLowerEmbedding` (M262.004) | Published `Langlands.NYLL.PortInternal.M262.d004` (imported, not redefined) |

Only the first row introduces a declaration in this module. Row M262.006 of the
published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../../../notes/reuse/nyll-public-port/m259-m262.md)
reserves `Langlands.NYLL.PortInternal.M262.d006` for this private source
theorem. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
adds `Statement` for a theorem's target. This is a fresh implementation name,
not the source's mangled private kernel name. The partition's predecessor
`M262.005.END` (`towerEmbeddedBaseNormClass`) is scheduling order only: the
statement does not mention it. No NYLL erratum for this module was found in the
current Library's `notes/`.

## Imports and modification record

The only direct import is the published
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U004.Definitions`,
which supplies `d004` and, through `Mathlib.FieldTheory.IsSepClosed`,
`SeparableClosure` and `AlgHom.fieldRange`. Every other transitive import lies
in the approved Mathlib environment. No external NYLL module is imported. The
source's broad imports, `IntrinsicAbsoluteData`, `NormResidueNaturality` and
`SeparableClosureEmbedding`, are not needed and are dropped.

The adaptation makes four changes:

- it moves the private theorem's telescope and conclusion into the public
  Prop-valued definition above, keeping binder order, binder kinds, binder
  names and the conclusion unchanged;
- it replaces `towerLowerEmbedding` by the published `d004`, which has the same
  arguments;
- it omits the source proof, the `private` modifier and every other declaration;
- it puts the definition in the namespace `Langlands.NYLL.PortInternal.M262`
  and keeps the source's `noncomputable section`.

The Lean header records these changes with Worker 30's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with no level
parameters and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not independent acceptance.

## Boundary and license

This file defines the proposition only. The proof, named
`Langlands.NYLL.PortInternal.M262.d006`, needs a separate proof task once this
target is in the Library. The source proof takes `x = iL (algebraMap E L y)`
and exhibits `algebraMap E L y` as its preimage under `iL`.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code. The imported U004 module and its Markdown are unchanged.
