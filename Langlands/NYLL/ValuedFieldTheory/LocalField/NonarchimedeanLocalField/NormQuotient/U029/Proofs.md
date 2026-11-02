# Norm-image membership gives trivial norm class

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOneOfMemStatement.{u}` with
the single named theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_one_of_mem`. It is the
proof phase of M093.029 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U029.Statements`.
That statement pair and its complete published dependency chain are unchanged.

## Exact target and mathematical meaning

The theorem's unapplied type is exactly

```lean
normClass_eq_one_of_mem : NormClassEqOneOfMemStatement.{u}
```

There are no external term or instance parameters. The published proposition
has the sole arbitrary universe `u` and unfolds to

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  {x : Kˣ} (hx : x ∈ localNormSubgroup K L), normClass K L x = 1
```

Its seven internal binders remain in source order: explicit `K` and `L`,
instance-implicit `Field K`, `Field L` and `Algebra K L`, implicit
representative `x`, and explicit membership witness `hx`. Introducing `x`
inside the proof does not change its implicit binder in the target.
There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise.

The public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, with independent field
universes and no finiteness premise. Here its universes specialize to the
shared `u`. The public `localNormSubgroup`, in
`NormQuotient.U001.Definitions`, is `(normUnits K L).range`. Thus `hx`
means that `x` is the norm of an actual extension-field unit.

The public `NormQuotient`, in U002.Definitions, is
`Kˣ ⧸ localNormSubgroup K L`; its public U003 commutative-group instance
supplies the identity. The public `normClass`, in U005.Definitions, is
`QuotientGroup.mk' (localNormSubgroup K L)`. The conclusion says that a
representative in the subgroup maps to the identity of this actual quotient.
All these constructions and their existing structures are reused unchanged.
The host `Langlands.LocalClassField.NormQuotient` has a finite-dimensionality
parameter and does not replace this general support interface.

## Implemented proof

The proof follows the original reverse-implication argument:

1. `intro K L _ _ _ x hx` introduces all seven internal binders of the
   published closed proposition, including its field and algebra instances.
2. The unchanged public U022.Proofs theorem
   `normClass_eq_one_iff_mem : NormClassEqOneIffMemStatement.{u}` specializes
   at `K L x` to
   `normClass K L x = 1 ↔ x ∈ localNormSubgroup K L`.
3. `(normClass_eq_one_iff_mem K L x).2 hx` applies its reverse implication
   to the supplied membership witness and closes the equality goal.

The theorem uses only this already proved equivalence. It adds no
construction, instance or simp registration.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:262–266`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L262-L266):
docstring at 262, theorem and complete telescope at 263–264, asserted
conclusion at 265, and proof at 266:

```lean
theorem normClass_eq_one_of_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] {x : Kˣ} (hx : x ∈ localNormSubgroup K L) :
    normClass K L x = 1 :=
  (normClass_eq_one_iff_mem K L x).2 hx
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The subgroup, quotient and canonical projection are at 26–54, and the
reused equivalence is at 206–211. The unit norm originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`; that complete
file was also read, with SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_eq_one_of_mem` | Named theorem `normClass_eq_one_of_mem : NormClassEqOneOfMemStatement.{u}`, proved here |
| Its telescope and asserted conclusion | Published closed `NormClassEqOneOfMemStatement.{u}` in U029.Statements, unchanged |
| Its reverse-implication proof | Same application after introducing the closed target's seven binders |
| `normClass_eq_one_iff_mem` | Public U022.Proofs theorem, unchanged |
| `localNormSubgroup` and `normUnits` | Existing public actual norm-image constructions, unchanged |
| `NormQuotient` and `normQuotientCommGroup` | Existing public quotient and group structure, unchanged |
| `normClass` | Existing public canonical projection, unchanged |

Worker 107 adapted this proof directly from the pinned original on
1 November 2026 and wrote this companion. The namespace gains the
`Langlands.NYLL` prefix; the source binders are introduced inside the
proof of the already published closed proposition. The sole
U029.Statements import preserves the public predecessor chain.
The original noncomputable section, unused universe `v` and unrelated
declarations are omitted. M093 has no patch10 change. No shared
adaptation draft or another worker's unpublished implementation was
reused; public dependency authorship remains unchanged.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
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

This generic norm-image implication leaves parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named `abelianLocalArtinMap`
family, exact norm kernel, host quotient construction and evaluation,
bijectivity, quotient topology, finite discrete Galois topology and both
continuity directions open, for every prime and arbitrary supplied
`TF`/`TE`. The initial Type 0 host stage does not discharge arbitrary-universe
transport. No normalization, inertia, cohomological comparison or
reciprocity theorem is proved here. Existing cohomological definitions
and frozen targets retain their meaning. M093.030 and later units and
host adapters remain separate work. Independent semantic acceptance and
Integrator publication are required before this is an accepted Library proof.
