# Subsingleton norm quotient for the identity extension

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientSelfSubsingletonStatement.{u}`
with the single named theorem
`Langlands.NYLL.LocalFieldTheory.normQuotient_self_subsingleton`.
It is the proof phase of M093.028 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U028.Statements`.
That statement pair and its complete public import chain are unchanged.

## Exact target and actual quotient

The theorem's unapplied type is exactly

```lean
normQuotient_self_subsingleton : NormQuotientSelfSubsingletonStatement.{u}
```

It has no external term or instance parameters and retains the sole
arbitrary universe `u`. The published proposition unfolds to

```lean
∀ (K : Type u) [Field K], Subsingleton (NormQuotient K K)
```

The two internal binders remain in order: explicit `K : Type u`, then
instance-implicit `[Field K]`. The canonical self-algebra is inferred
from the field structure. No arbitrary `[Algebra K K]`, finite-dimensionality,
finite-module, local-field, separability, Galois, valuation or topology
premise is supplied.

The reused public `Langlands.NYLL.LocalFieldTheory.NormQuotient`, in
`NormQuotient.U002.Definitions`, is `Kˣ ⧸ localNormSubgroup K L`.
The public `localNormSubgroup`, in U001.Definitions, is
`(normUnits K L).range`. The public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, with independent field
universes and no finiteness premise. The existing commutative-group
instance `normQuotientCommGroup`, in U003.Definitions, supplies the
quotient identity. All these declarations are reused unchanged.

Thus this theorem concerns the actual quotient of `Kˣ` by the image of
the identity-extension unit norm. It proves that any two of its classes
are equal. The existing group identity also makes the quotient inhabited.
The proved target itself is exactly the displayed `Subsingleton` assertion.

## Implemented proof and instance use

`Subsingleton` is a Prop-valued class, whose field `allEq` asserts equality
of any two elements. The implementation proves this class:

1. `intro K _` introduces the closed target's field and field instance.
2. The structure expression supplies its sole field `allEq`. For arbitrary
   `x y : NormQuotient K K`, the goal is `x = y`.
3. `rw [normQuotient_self_eq_one K x, normQuotient_self_eq_one K y]`
   uses the public U027.Proofs theorem twice. That theorem has the closed
   type `NormQuotientSelfEqOneStatement.{u}`, which unfolds to
   `∀ (K : Type u) [Field K] (x : NormQuotient K K), x = 1`.
   The rewrites replace both classes by the identity, and reflexivity
   closes the resulting equality.

This retains the original source's complete `allEq` proof. It constructs
a proof of a Prop-valued class, without constructing a new norm, subgroup
or quotient. The theorem is declared with `theorem`, without an instance
attribute or simp registration. It installs no global, scoped or local
instance. After publication a client may apply the theorem to its field
and install the result locally as needed:

```lean
letI : Subsingleton (NormQuotient K K) := normQuotient_self_subsingleton K
```

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:256–260`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L256-L260):
docstring at 256, instance name and complete telescope at 257,
asserted class at 258, and `allEq` proof at 259–260.
The original declaration is

```lean
instance normQuotient_self_subsingleton (K : Type u) [Field K] :
    Subsingleton (NormQuotient K K) where
  allEq x y := by
    rw [normQuotient_self_eq_one K x, normQuotient_self_eq_one K y]
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
It also defines the subgroup, quotient and group structure at 26–38
and proves `normQuotient_self_eq_one` at 247–254.
The unit norm originates in `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`;
that complete file was also read, with SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Prop-valued instance `normQuotient_self_subsingleton` | Named theorem `normQuotient_self_subsingleton : NormQuotientSelfSubsingletonStatement.{u}`, proved here |
| Its telescope and asserted class | Published closed `NormQuotientSelfSubsingletonStatement.{u}` in U028.Statements, unchanged |
| Its `allEq` proof | Same two rewrites after introducing the closed target's binders |
| Global instance registration | Optional local installation by future clients |
| `normQuotient_self_eq_one` | Public U027.Proofs theorem, unchanged |
| `NormQuotient` | Public U002.Definitions construction, unchanged |
| `normQuotientCommGroup` | Public U003.Definitions instance, unchanged |
| `localNormSubgroup` | Public U001.Definitions construction, unchanged |
| `normUnits` | Public NormUnits.U002.Definitions construction, unchanged |

Worker 107 adapted this proof directly from the pinned original on
1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix; the two original binders are introduced inside
the proof of the published closed proposition. The source instance
becomes a named theorem. The sole U028.Statements import preserves the
published predecessor chain. The original noncomputable section, unused
universe `v` and other declarations are omitted. M093 has no patch10
change. No shared adaptation draft or another worker's unpublished
implementation was reused; public dependency authorship is retained.

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

## Attribution and scope

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. There are no
additional project coauthors or reused-draft contributors. The inherited
Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

This generic quotient theorem leaves parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named `abelianLocalArtinMap`,
actual unit-norm image, exact norm kernel, host quotient construction,
evaluation, bijectivity, quotient and finite discrete Galois topologies,
and both continuity directions open, for every prime and arbitrary
supplied `TF`/`TE`. The initial Type 0 host stage does not discharge
arbitrary-universe transport. No normalization, inertia, cohomological
comparison or reciprocity theorem is proved here. Existing cohomological
definitions and frozen targets retain their meaning. M093.029 and later
units, new constructions, simp registrations and host adapters remain
separate work. Compilation requires independent semantic review and
Integrator publication before this result is an accepted Library proof.
