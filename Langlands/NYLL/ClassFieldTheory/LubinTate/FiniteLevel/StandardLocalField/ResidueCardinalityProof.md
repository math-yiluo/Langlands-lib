# Residue cardinality of the canonical local-field package (M335.004)

This module proves the published proposition
`Langlands.NYLL.LubinTate.standardLocalField_residueField_natCardStatement`
by the theorem
`Langlands.NYLL.LubinTate.standardLocalField_residueField_natCard`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Statements`.

## Statement and parameters

The theorem has the fully applied imported target as its result:

```lean
standardLocalField_residueField_natCardStatement K
```

Unfolding that proposition gives

```lean
Nat.card (standardLocalField K).residueField = Nat.card 𝓀[K]
```

The complete telescope is exactly

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

In particular, `K` is explicit and in universe 0, and the theorem adds no
hypothesis. The source `@[simp]` attribute is retained. The scoped
`ValuativeRel` notation `𝓀[K]` denotes
`IsLocalRing.ResidueField ↥𝒪[K]`, the residue field of the canonical
valuation ring of `K`.

## Implemented proof

The proof term is the source's `rfl`. Reduction of the imported proposition,
the canonical package `standardLocalField K`, and its residue-field
accessors identifies the left-hand residue field definitionally with
`𝓀[K]`. Both sides are then the same application of `Nat.card`, so
reflexivity proves the target.

The proof reuses the published canonical `standardLocalField` and
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF`; it introduces no
alternative package or residue-field equivalence. Finiteness is already
part of the canonical local-field package under the displayed local-field
assumption. No auxiliary lemma is needed.

## Source and attribution

The source is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L66-L72)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, unit M335.004,
lines 66–72 (theorem statement at lines 69–71). The source telescope is
at lines 37–38. The file's SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.

The readable pinned snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The public errata directory contains no entry named for either source,
and the public NYLL port plan lists no patch10 compatibility edit for
this source module.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 238 made these modifications on 16 November 2026:

- extracted only M335.004 with its original docstring, `@[simp]` attribute
  and `rfl` proof;
- prefixed the namespace `LubinTate` with `Langlands.NYLL`;
- expressed the theorem's result as the fully applied published
  `standardLocalField_residueField_natCardStatement K`;
- replaced the six broad source imports by the one focused import above;
- omitted the four source namespace opens, which this extracted proof
  does not use, and retained `noncomputable section` and
  `open scoped ValuativeRel`;
- replaced the module documentation, added a prominent modification
  notice, and wrote this paired Markdown.

The source telescope is unchanged, and no compatibility patch or additional
hypothesis is introduced. The published statement pair and its imports
are preserved.
