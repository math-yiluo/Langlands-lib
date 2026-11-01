# Unit norm for the identity extension

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.NormUnitsSelfApplyStatement.{u} : Prop`.
It is the statement phase of M093.025 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U024.Proofs`.

## Complete interface and mathematical meaning

The definition has no external term or instance parameters and retains the
sole arbitrary universe `u`. Its entire body is:

```lean
∀ (K : Type u) [Field K] (x : Kˣ), normUnits K K x = x
```

All three binders are inside the proposition: the explicit field type
`K : Type u`, its instance `[Field K]`, and the explicit unit `x : Kˣ`,
in that order. The equality is an equality of units in `Kˣ`.
The canonical algebra structure of a field over itself is inferred from
the field structure. An arbitrary supplied `[Algebra K K]` is not quantified.
There is no finite-dimensionality, valuation, topology, local-field,
separability or Galois hypothesis.

The already public
`Langlands.NYLL.LocalFieldTheory.normUnits` in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`
is unchanged. For general fields its definition is
`normUnits K L = Units.map (Algebra.norm K)`; its field universes are
independent and it requires no finite-dimensionality assumption.
Here both arguments are `K` with the canonical self-algebra, so the
assertion says that the norm for the identity extension sends every unit
to itself. This file defines that assertion without supplying a proof
of its truth.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:231–235`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L231-L235):
docstring at line 231, theorem name and complete telescope at 232,
equation at 233, and proof at 234–235.
The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its theorem has exactly
`(K : Type u) [Field K] (x : Kˣ) : normUnits K K x = x`.
The source proves this using unit extensionality followed by
`simp [normUnits]`; that proof is omitted in this statement phase.
The existing unit norm comes from
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`,
whose whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
That complete original file was also read.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Assertion of `normUnits_self_apply` | Closed `NormUnitsSelfApplyStatement.{u}` defined here |
| `normUnits` | Existing public U002.Definitions construction, unchanged |

Worker 107 adapted the assertion directly from the pinned original on
1 November 2026, added the namespace prefix and closed the original three
binders inside a Prop-valued definition. The sole U024.Proofs import
retains the published predecessor chain. The original proof, noncomputable
section, unused universe `v` and unrelated declarations are omitted.
No new theorem, instance, simp registration, replacement norm definition
or later source unit is introduced. M093 has no feasibility patch10 change.
No shared adaptation draft or other worker's unpublished work was reused.

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
this statement and wrote this companion. There are no other project
coauthors or reused-draft contributors; dependency authors and notices
remain unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
they match the originals, including inherited dependency notices.

This generic identity-extension assertion supplies no named Artin map,
actual norm-kernel theorem for that map, host reciprocity quotient
equivalence, host evaluation formula or continuity theorem. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains its named Artin family,
every-prime and arbitrary supplied `TF`/`TE` requirements, actual unit-norm
image, quotient topology and finite discrete Galois topology obligations.
The initial Type 0 host stage does not discharge arbitrary-universe
transport. No normalization, inertia, cohomological comparison or
reciprocity theorem follows from this statement. Existing cohomological
definitions and frozen targets retain their meaning.
The proof of M093.025, M093.026 and later units, and host adapters require
separate work. Compilation does not establish independent semantic
acceptance or publication.
