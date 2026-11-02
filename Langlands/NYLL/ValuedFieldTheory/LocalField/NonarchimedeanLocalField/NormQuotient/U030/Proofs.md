# Integer powers of unit norms have trivial norm class

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassNormUnitsZpowEqOneStatement.{u}`
with the single named theorem
`Langlands.NYLL.LocalFieldTheory.normClass_normUnits_zpow_eq_one`.
It is the proof phase of M093.030 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U030.Statements`.
That statement pair and its complete published dependency chain remain unchanged.

## Exact target and mathematical meaning

The theorem's unapplied type is exactly

```lean
normClass_normUnits_zpow_eq_one : NormClassNormUnitsZpowEqOneStatement.{u}
```

There are no external term or instance parameters. The published proposition
has the sole arbitrary universe `u` and unfolds to

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) (n : Int),
  normClass K L ((normUnits K L x) ^ n) = 1
```

All seven internal binders remain in source order: explicit `K` and `L`,
instance-implicit `Field K`, `Field L` and `Algebra K L`, explicit unit `x`,
and explicit integer exponent `n`. The exponent includes positive, zero and
negative integers. The power is formed in `Kˣ` before applying `normClass`;
zero gives the identity unit and negative powers use inversion.
There is no finite-dimensionality, finite-module, local-field, separability,
Galois, valuation or topology premise.

The public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, without a finiteness premise.
Its independent field universes specialize here to the common `u`.
The public `localNormSubgroup`, in `NormQuotient.U001.Definitions`, is
`(normUnits K L).range`. The public `NormQuotient`, in U002.Definitions,
is `Kˣ ⧸ localNormSubgroup K L`, with its existing U003 commutative-group
structure. The public `normClass`, in U005.Definitions, is the canonical
homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`.

Thus every integer power of an actual unit norm has the identity class in
the actual quotient by the unit-norm image. The equality and its `1` lie
in that quotient. These constructions and structures are reused unchanged.
The host `Langlands.LocalClassField.NormQuotient` has a finite-dimensionality
premise and does not replace this general support interface.

## Implemented proof

The proof follows the original three rewrites:

1. `intro K L _ _ _ x n` introduces all seven internal binders of the
   closed proposition, including the field and algebra instances.
2. `map_zpow` moves the integer power through the group homomorphism
   `normClass K L`, giving
   `(normClass K L (normUnits K L x)) ^ n = 1`.
3. The unchanged public U017.Proofs theorem
   `mk_normUnits_eq_one : MkNormUnitsEqOneStatement.{u}`, specialized to
   `K L x`, rewrites the base of this power to `1`.
4. `one_zpow` gives `1 ^ n = 1` for every integer `n` and closes the goal.

The exact implementation is

```lean
intro K L _ _ _ x n
rw [map_zpow, mk_normUnits_eq_one, one_zpow]
```

The inherited theorem is available through U030.Statements' complete public
chain. No construction, instance or simp registration is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:268–272`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L268-L272):
docstring at 268, theorem name at 269, complete telescope at 270, asserted
conclusion at 271, and proof at 272:

```lean
theorem normClass_normUnits_zpow_eq_one
    (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) (n : Int) :
    normClass K L ((normUnits K L x) ^ n) = 1 := by
  rw [map_zpow, mk_normUnits_eq_one, one_zpow]
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The subgroup, quotient and canonical projection are at 26–54, and the
reused `mk_normUnits_eq_one` is at 171–174. The unit norm originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`; that complete
original file was also read, with SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_normUnits_zpow_eq_one` | Named theorem `normClass_normUnits_zpow_eq_one : NormClassNormUnitsZpowEqOneStatement.{u}`, proved here |
| Its telescope and asserted conclusion | Published closed `NormClassNormUnitsZpowEqOneStatement.{u}` in U030.Statements, unchanged |
| Its three-rewrite proof | Same rewrites after introducing the closed target's seven binders |
| `mk_normUnits_eq_one` | Public U017.Proofs theorem, unchanged |
| `normUnits` and `localNormSubgroup` | Existing public actual norm-image constructions, unchanged |
| `NormQuotient` and `normQuotientCommGroup` | Existing public quotient and group structure, unchanged |
| `normClass` | Existing public canonical projection, unchanged |

Worker 107 adapted this proof directly from the pinned original on
1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix; the source binders are introduced inside the
proof of the already published closed proposition. The sole
U030.Statements import preserves the public predecessor chain.
The original noncomputable section, unused universe `v` and unrelated
declarations are omitted. M093 has no patch10 change. No shared
adaptation draft or another worker's unpublished implementation was reused;
public dependency authorship remains unchanged.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked in the workspace, project and
supplied Library; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. There are no other
project coauthors or reused-draft contributors. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain unchanged
through `repository_paths`; their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
including inherited dependency attribution.

This generic algebraic fact leaves parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named `abelianLocalArtinMap`
family, exact norm kernel, host quotient/evaluation and bijectivity,
actual quotient and finite discrete Galois topologies, and both continuity
directions open. Initial host Type 0 does not discharge arbitrary-universe
transport. It supplies no normalization, inertia, cohomological comparison or
reciprocity theorem. Existing cohomological definitions and frozen targets
retain their meaning. M093.031 onward and host adapters remain separate work.
Compilation alone establishes neither independent semantic acceptance nor
Integrator publication.
