# Field range of the compatible lower embedding: proof

`Langlands.NYLL.PortInternal.M262.d006` proves the published target
`Langlands.NYLL.PortInternal.M262.d006Statement` for every choice of its
parameters:

```lean
theorem d006
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    d006Statement K E L iL
```

So for a tower `K → E → L` and a `K`-embedding `iL` of `L` into the separable
closure of `K`, the field range of the restricted embedding
`Langlands.NYLL.PortInternal.M262.d004 K E L iL = iL.comp (IsScalarTower.toAlgHom K E L)`
is contained in the field range of `iL`.

## Proof

The proof is the source proof, unchanged. The target unfolds to an inclusion of
intermediate fields of `SeparableClosure K`. Take `x` in the range of
`d004 K E L iL` and write it as the image of some `y : E` (`rcases hx with ⟨y, rfl⟩`).
Then `x = iL (algebraMap E L y)` by definition of `d004`, so `algebraMap E L y`
is a preimage under `iL`; the membership proof is `rfl`.

## Source and modifications

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`
(SHA-256 `a81fa466df15d0d72f24428f0780a68b9a9f434fa4d27746beafe71bfae521c0`),
private theorem `towerEmbeddedFieldRange_le` at lines 66–76 (inventory M262.006).
The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `towerLowerEmbedding` (private, M262.004) | `Langlands.NYLL.PortInternal.M262.d004` (published, reused by name) |
| `towerEmbeddedFieldRange_le` (private, M262.006) | `Langlands.NYLL.PortInternal.M262.d006` |

Modifications: the private theorem becomes the public
`Langlands.NYLL.PortInternal.M262.d006`, following the port's naming rule for
private source commands; the conclusion is written as the published target
applied to the telescope; the only import is the statement module. The namespace changes from `LocalClassFieldTheory` to
`Langlands.NYLL.PortInternal.M262`, and the source's `noncomputable section` is
retained. The source imports `Mathlib.GroupTheory.Abelianization.Defs`,
`Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding`,
`Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData`
and `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality`
are replaced by the published U006 statement import. That statement imports
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U004.Definitions`,
whose only direct import is `Mathlib.FieldTheory.IsSepClosed`. There are no
other NYLL imports. The source namespace openings and unrelated declarations
are omitted. The telescope and tactic proof are unchanged; all fields remain
in `Type 0`, with no extra hypotheses. The source theorem has no docstring; the
docstring is the one of the published statement.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Worker 294 also compiled and inspected the submitted module on 13 November
2026 (diagnostic `d07b8c64-40d8-4c80-a552-15ed8afce2f7`), with zero errors and
zero warnings. Inspection identifies a theorem with no universe parameters
and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Development checks are not independent acceptance; the submission boundary
checks the exact published target.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted by
OpenAI Codex). It remains under Apache-2.0. The already-published `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` are reused unchanged and included through
`repository_paths`. Worker 89 adapted this proof directly from the pinned original;
Worker 294 prepared the submitted pair from Worker 89's shared Task 5881
draft on 13 November 2026, checking it against the original and the current
Library without changing the theorem or proof. The statement and its imported
definition are reused unchanged. This helper asserts only field-range
inclusion; it makes no local reciprocity or host-comparison claim.
