# Norm subgroup for the identity extension

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.LocalNormSubgroupSelfStatement.{u} : Prop`.
It records the assertion of M093.026 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U025.Proofs`.
That module and its complete published chain remain unchanged.

## Complete closed telescope and mathematical meaning

The definition has no external term or instance parameters and retains
exactly the arbitrary universe `u`. Its entire body is

```lean
∀ (K : Type u) [Field K], localNormSubgroup K K = ⊤
```

The two internal binders, in order, are the explicit field type `K` and
the instance-implicit field structure `[Field K]`. The equality is in
`Subgroup Kˣ`; `⊤` is the subgroup of all units of `K`.
The canonical self-algebra of `K` is inferred from the field structure.
There is no arbitrary supplied `[Algebra K K]`, finite-dimensionality,
valuation, topology, local-field, separability or Galois premise.
The name's local-field context does not restrict this generic assertion.

The reused public
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup`, in
`NormQuotient.U001.Definitions`, is exactly `(normUnits K L).range`
for same-universe fields with an algebra structure. The existing public
`Langlands.NYLL.LocalFieldTheory.normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, with independent field
universes and no finite-dimensionality parameter. These constructions
are unchanged. Thus membership of `x : Kˣ` in the subgroup on the left
means that there exists `y : Kˣ` with `normUnits K K y = x`.
The proposition asserts that every base-field unit belongs to this actual
image for the identity extension.

The imported public `normUnits_self_apply` establishes that the
identity-extension unit norm fixes every unit. It is a prerequisite for
the later proof phase; this module only defines the proposition.
It contains no truth proof, new norm construction, instance or host adapter.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:237–245`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L237-L245):
docstring at 237, `localNormSubgroup_self` and its complete telescope at
238, equation at 239, and the omitted proof at 240–245. The original is

```lean
theorem localNormSubgroup_self (K : Type u) [Field K] :
    localNormSubgroup K K = ⊤
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The same file defines the norm subgroup at lines 26–28 and proves the
predecessor `normUnits_self_apply` at lines 231–235. The support norm
originates in `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`.
That complete original file was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Telescope and equation of `localNormSubgroup_self` | Closed `LocalNormSubgroupSelfStatement.{u}`, defined here |
| `localNormSubgroup` | Existing public U001.Definitions construction, unchanged |
| `normUnits` | Existing public NormUnits.U002.Definitions construction, unchanged |
| `normUnits_self_apply` | Existing public U025.Proofs theorem, unchanged |
| Proof of `localNormSubgroup_self` | Deferred to a separate proof phase |

Worker 107 extracted this assertion directly from the pinned original
on 1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix, the original binders move inside the closed
Prop-valued definition, and the sole U025.Proofs import preserves the
predecessor chain. The original proof, noncomputable section, unused
universe `v` and unrelated declarations are omitted. There is no new data
construction, instance, M093.027 or later unit, or host adapter.
M093 has no patch10 change. No shared adaptation draft or another
worker's unpublished work was reused.

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

The truth proof of this proposition requires separate independent
acceptance and publication after the statement phase.
Parent task `1cbd1968-d285-4b34-822c-f6b5599d1c38` retains one named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, with the actual unit-norm image, exact norm kernel, quotient
topology, finite discrete Galois topology, host quotient construction,
evaluation, bijectivity and both continuity directions. Type 0 is the
initial host stage and does not discharge arbitrary-universe transport.
This generic support statement supplies no normalization, inertia,
cohomological comparison or reciprocity theorem. Existing cohomological
definitions and frozen targets retain their meaning. Later M093 units
and host adapters remain separate work. Compilation alone establishes
neither independent semantic acceptance nor publication.
