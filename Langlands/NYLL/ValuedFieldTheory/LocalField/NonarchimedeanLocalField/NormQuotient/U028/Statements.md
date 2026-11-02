# Subsingleton norm quotient for the identity extension

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientSelfSubsingletonStatement.{u} : Prop`.
It records the asserted type of M093.028 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U027.Proofs`.
That module and its complete published chain remain unchanged.

## Complete closed telescope and actual quotient

The definition has no external term or instance parameters and retains
exactly the arbitrary universe `u`. Its entire body is

```lean
∀ (K : Type u) [Field K], Subsingleton (NormQuotient K K)
```

The two internal binders, in order, are explicit `K : Type u` and
instance-implicit `[Field K]`. The canonical self-algebra of `K` is
inferred from its field structure. There is no supplied arbitrary
`[Algebra K K]`, finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise. The module's local-field
context does not restrict this generic assertion.

The public `Langlands.NYLL.LocalFieldTheory.NormQuotient`, in
`NormQuotient.U002.Definitions`, is exactly
`Kˣ ⧸ localNormSubgroup K L` for same-universe fields with an algebra
structure. The public `localNormSubgroup`, in U001.Definitions, is
`(normUnits K L).range`. The public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, with independent field
universes and no finiteness premise. The public commutative-group instance
`normQuotientCommGroup`, in U003.Definitions, is also preserved.
All four declarations are reused unchanged.

Thus the proposition concerns the actual quotient of `Kˣ` by the range
of the identity-extension unit norm `normUnits K K`. It asserts that any
two elements of this quotient are equal. The existing group structure
supplies an identity element, so this actual quotient is inhabited;
the target itself is precisely the displayed `Subsingleton` assertion.

## Prop-valued instance and deferred proof

The original source command is an `instance` with asserted type
`Subsingleton (NormQuotient K K)`. `Subsingleton` is a Prop-valued class:
its `allEq` field states equality of any two elements. Proving this class
is a truth assertion, rather than a new quotient or other data
construction. This resolves the partition's `B1:instance?` as a statement
phase followed by an exact proof phase.

This file only defines that closed proposition. It installs no global,
scoped or local instance and contains no truth proof. The later exact
proof is reserved as the named theorem
`Langlands.NYLL.LocalFieldTheory.normQuotient_self_subsingleton`, with
type `NormQuotientSelfSubsingletonStatement.{u}`. Once that theorem is
independently published, clients may apply it to their field and install
the result locally as a `Subsingleton (NormQuotient K K)` instance.
This preserves the source mathematical assertion without introducing
a competing global instance.

The imported public theorem `normQuotient_self_eq_one` in U027.Proofs
proves that every element of this quotient equals its identity. The
original source's `allEq` proof rewrites both elements with that theorem.
This describes the source proof and the dependency for a later proof
task; this statement module does not implement or publish that proof.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:256–260`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L256-L260):
docstring at 256, instance name and complete telescope at 257, asserted
class at 258, and omitted `allEq` proof at 259–260. Its asserted type is

```lean
instance normQuotient_self_subsingleton (K : Type u) [Field K] :
    Subsingleton (NormQuotient K K)
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The same file defines the norm subgroup at 26–28, quotient at 30–32
and commutative-group structure at 34–38, and proves the predecessor
`normQuotient_self_eq_one` at 247–254. The support norm originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`. That complete
original file was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Telescope and asserted class of instance `normQuotient_self_subsingleton` | Closed `NormQuotientSelfSubsingletonStatement.{u}`, defined here |
| `NormQuotient` | Existing public U002.Definitions construction, unchanged |
| `normQuotientCommGroup` | Existing public U003.Definitions instance, unchanged |
| `localNormSubgroup` | Existing public U001.Definitions construction, unchanged |
| `normUnits` | Existing public NormUnits.U002.Definitions construction, unchanged |
| `normQuotient_self_eq_one` | Existing public U027.Proofs theorem, unchanged |
| Instance's `allEq` truth proof | Deferred named theorem `normQuotient_self_subsingleton` in a later proof phase |
| Global instance registration | Replaced by optional local installation of the later named theorem by clients |

Worker 107 extracted the asserted type directly from the pinned original
on 1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix, both original binders move inside the closed
Prop-valued definition, and the sole U027.Proofs import preserves the
complete published chain. The truth proof, instance registration,
noncomputable section, unused universe `v` and unrelated declarations
are omitted. M093 has no patch10 change. No shared adaptation draft or
another worker's unpublished work was reused.

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

The exact truth proof requires separate independent acceptance and
publication after this statement phase. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains one named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, with the actual unit-norm image, exact norm kernel, quotient
topology, finite discrete Galois topology, host quotient construction,
evaluation, bijectivity and both continuity directions. Type 0 is the
initial host stage and does not discharge arbitrary-universe transport.
This generic support statement supplies no normalization, inertia,
universe transport, cohomological comparison or reciprocity theorem.
Existing cohomological definitions and frozen targets retain their
meaning. M093.029 and later units and host adapters remain separate work.
Compilation alone establishes neither independent semantic acceptance
nor publication.
