# Unit norm for the identity extension

This module proves the exact published closed target
`Langlands.NYLL.LocalFieldTheory.NormUnitsSelfApplyStatement.{u}` with the
single theorem
`Langlands.NYLL.LocalFieldTheory.normUnits_self_apply`.
It is the proof phase of M093.025 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U025.Statements`.
That module's Lean/Markdown pair and all imported pairs are unchanged.

## Complete interface and implemented proof

The theorem has exactly this unapplied type:

```lean
normUnits_self_apply : NormUnitsSelfApplyStatement.{u}
```

It has no external term or instance parameters and retains the sole
arbitrary universe `u`. The published proposition unfolds to

```lean
∀ (K : Type u) [Field K] (x : Kˣ), normUnits K K x = x
```

The three binders are internal, in the order explicit `K`, instance-implicit
`Field K`, explicit unit `x`. The equality is in `Kˣ`. The canonical
self-algebra of `K` is inferred from the field structure; there is no supplied
arbitrary `[Algebra K K]`. No finite-dimensionality, valuation, topology,
local-field, separability or Galois hypothesis is added.

The implementation introduces these three binders with `intro K _ x`.
Unit extensionality (`ext`) reduces the goal to equality of the underlying
field elements. Then `simp [normUnits]` unfolds the existing support norm,
which is `Units.map (Algebra.norm K)`, and uses Mathlib's
`Algebra.norm_self : Algebra.norm K = MonoidHom.id K`. Evaluating the identity
homomorphism gives the underlying element of `x`, completing the equality.
Thus the algebra norm of the identity extension fixes each unit. The
self-norm theorem is available at the approved Mathlib pin in
`Mathlib/RingTheory/Norm/Defs.lean:67–69`, following the determinant norm
definition at lines 59–62. No new norm construction or helper lemma is needed.

The reused public support definition is
`Langlands.NYLL.LocalFieldTheory.normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`.
It uses independent field universes and has no finite-dimensionality
parameter. This proof preserves that interface.

## Pinned original and theorem map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:231–235`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L231-L235):
docstring at 231, theorem and complete telescope at 232, equation at 233,
and the `ext` / `simp [normUnits]` proof at 234–235. The complete original
file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The original has exactly
`(K : Type u) [Field K] (x : Kˣ) : normUnits K K x = x`.
The existing norm definition originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`,
whose complete file was also read and has SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normUnits_self_apply` | `normUnits_self_apply : NormUnitsSelfApplyStatement.{u}`, proved here |
| Its theorem telescope and equation | Existing closed `NormUnitsSelfApplyStatement.{u}`, unchanged |
| `normUnits` | Existing public U002.Definitions construction, unchanged |

Worker 107 adapted the proof directly from the pinned original on
1 November 2026. The namespace gains the `Langlands.NYLL` prefix, the
theorem proves the already published proposition by introducing its original
three binders, and the original extensionality and simplification proof
is retained. The sole U025.Statements import preserves the predecessor
chain. The noncomputable section, unused universe `v` and all unrelated
declarations are omitted. There is no new statement, instance, simp
registration, later source unit or host adapter. M093 has no patch10 change.
No shared adaptation draft or another worker's unpublished work was reused.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked in the workspace, project and
supplied Library; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. Worker 107 adapted
this proof and wrote this companion. There are no other project coauthors
or reused-draft contributors; dependency authors and notices remain
unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
they match the originals, including inherited dependency notices.

This generic identity-extension proof supplies no named Artin map,
actual norm-kernel theorem for that map, host reciprocity quotient
equivalence, host evaluation formula or continuity theorem. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains its named Artin family,
every-prime and arbitrary supplied `TF`/`TE` requirements, actual unit-norm
image, exact norm kernel, quotient topology, finite discrete Galois topology,
host quotient construction/evaluation/bijectivity and both continuity
directions. The initial Type 0 host stage does not discharge
arbitrary-universe transport. No normalization, inertia, cohomological
comparison or reciprocity theorem follows from this proof. Existing
cohomological definitions and frozen targets retain their meaning.
M093.026 and later units and host adapters require separate work.
Compilation does not establish independent semantic acceptance or publication.
