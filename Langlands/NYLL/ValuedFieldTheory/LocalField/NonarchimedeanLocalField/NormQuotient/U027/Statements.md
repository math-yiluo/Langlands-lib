# Norm classes for the identity extension

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientSelfEqOneStatement.{u} : Prop`.
It records the assertion of M093.027 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U026.Proofs`.
That module and its complete published chain remain unchanged.

## Complete closed telescope and actual quotient

The definition has no external term or instance parameters. It retains
exactly the arbitrary universe `u`, and its entire body is

```lean
∀ (K : Type u) [Field K] (x : NormQuotient K K), x = 1
```

The three internal binders, in order, are the explicit field type `K`,
the instance-implicit field structure `[Field K]`, and the explicit norm
class `x : NormQuotient K K`. The canonical self-algebra of `K` is inferred
from its field structure. There is no supplied arbitrary `[Algebra K K]`,
finite-dimensionality, valuation, topology, local-field, separability or
Galois premise. The module's local-field context does not restrict this
generic assertion.

The public `Langlands.NYLL.LocalFieldTheory.NormQuotient`, in
`NormQuotient.U002.Definitions`, is exactly
`Kˣ ⧸ localNormSubgroup K L` for same-universe fields with an algebra
structure. Its public commutative-group structure
`normQuotientCommGroup`, in U003.Definitions, supplies the identity `1`
used here. The public `localNormSubgroup`, in U001.Definitions, is
`(normUnits K L).range`. The public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`; it has independent field
universes and no finite-dimensionality premise. All four declarations
are reused unchanged.

Thus `x` belongs to the actual quotient of `Kˣ` by the image of the unit
norm for the identity extension. The equation `x = 1` is equality in
that quotient, with its existing group identity. It asserts that every
such quotient class is the identity class.

The imported public `localNormSubgroup_self` proves that the
identity-extension norm image is all of `Kˣ`. It is available for the
later proof phase. This module only defines the proposition; the truth
proof and the later subsingleton instance are separate work.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:247–254`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L247-L254):
docstring at 247, theorem and its complete telescope at 248, equation at
249, and the omitted proof at 250–254. The original assertion is

```lean
theorem normQuotient_self_eq_one (K : Type u) [Field K] (x : NormQuotient K K) :
    x = 1
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The same file defines the norm subgroup at 26–28, quotient at 30–32
and commutative-group structure at 34–38, and proves the predecessor
`localNormSubgroup_self` at 237–245. The support norm originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`. That complete
original file was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Telescope and equation of `normQuotient_self_eq_one` | Closed `NormQuotientSelfEqOneStatement.{u}`, defined here |
| `NormQuotient` | Existing public U002.Definitions construction, unchanged |
| `normQuotientCommGroup` | Existing public U003.Definitions instance, unchanged |
| `localNormSubgroup` | Existing public U001.Definitions construction, unchanged |
| `normUnits` | Existing public NormUnits.U002.Definitions construction, unchanged |
| `localNormSubgroup_self` | Existing public U026.Proofs theorem, unchanged |
| Proof of `normQuotient_self_eq_one` | Deferred to a separate proof phase |

Worker 107 extracted this assertion directly from the pinned original
on 1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix, the original binders move inside the closed
Prop-valued definition, and the sole U026.Proofs import preserves the
entire published chain. The original proof, noncomputable section,
unused universe `v` and unrelated declarations are omitted. There is
no new norm or quotient construction, instance, M093.028 or later unit,
or host adapter. M093 has no patch10 change. No shared adaptation draft
or another worker's unpublished work was reused.

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
Codex)”, with an explicit dated modification record. There are no other
project coauthors or reused-draft contributors; dependency authors and
notices remain unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
they match the originals, including inherited dependency notices.

The truth proof requires separate independent acceptance and publication
after this statement phase. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains one named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, with the actual unit-norm image, exact norm kernel, quotient
topology, finite discrete Galois topology, host quotient construction,
evaluation, bijectivity and both continuity directions. Type 0 is the
initial host stage and does not discharge arbitrary-universe transport.
This generic support statement supplies no normalization, inertia,
universe transport, cohomological comparison or reciprocity theorem.
Existing cohomological definitions and frozen targets retain their
meaning. M093.028 and later units and host adapters remain separate work.
Compilation alone establishes neither independent semantic acceptance
nor publication.
