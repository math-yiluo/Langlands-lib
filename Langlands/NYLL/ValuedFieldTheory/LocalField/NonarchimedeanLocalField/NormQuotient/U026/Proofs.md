# Norm subgroup for the identity extension

This module proves the exact published closed target
`Langlands.NYLL.LocalFieldTheory.LocalNormSubgroupSelfStatement.{u}` with the
single theorem
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup_self`.
It is the proof phase of M093.026 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U026.Statements`.
That module's Lean/Markdown pair and all imported pairs are unchanged.

## Complete interface and mathematical meaning

The theorem has exactly this unapplied type:

```lean
localNormSubgroup_self : LocalNormSubgroupSelfStatement.{u}
```

It has no external term or instance parameters and retains the sole
arbitrary universe `u`. The published proposition unfolds to

```lean
∀ (K : Type u) [Field K], localNormSubgroup K K = ⊤
```

The two binders are internal, in the order explicit `K` and
instance-implicit `Field K`. The equality is in `Subgroup Kˣ`, where `⊤` is
the subgroup of all units of `K`. The canonical self-algebra of `K` is
inferred from the field structure; there is no supplied arbitrary
`[Algebra K K]`. No finite-dimensionality, finite-module, valuation,
topology, local-field, separability or Galois hypothesis is added. The
name's local-field context does not restrict this generic result.

The reused public `Langlands.NYLL.LocalFieldTheory.localNormSubgroup`, in
`NormQuotient.U001.Definitions`, is exactly `(normUnits K L).range`. The
public `Langlands.NYLL.LocalFieldTheory.normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`. Both are unchanged. So a unit
`x : Kˣ` lies in `localNormSubgroup K K` exactly when some `y : Kˣ` satisfies
`normUnits K K y = x`. The theorem says that this actual image of the unit
norm of `K` over itself is all of `Kˣ`: every base-field unit is a norm for
the identity extension.

## Implemented proof

The implementation introduces the two binders with `intro K _` and then
keeps the original proof unchanged:

1. `ext x` applies subgroup extensionality. It reduces the goal to
   `x ∈ localNormSubgroup K K ↔ x ∈ ⊤` for an arbitrary unit `x : Kˣ`.
2. `constructor` splits the equivalence into its two directions.
3. Forward direction: every unit lies in the top subgroup. This is Mathlib's
   `Subgroup.mem_top x`, at the approved pin in
   `Mathlib/Algebra/Group/Subgroup/Lattice.lean:143`.
4. Reverse direction: the anonymous constructor `⟨x, normUnits_self_apply K x⟩`
   uses `x` itself as the norm witness. Membership in the range of a
   monoid homomorphism unfolds definitionally to the existence of a
   preimage. Mathlib's `MonoidHom.range` at
   `Mathlib/Algebra/Group/Subgroup/Ker.lean:66–67` has carrier
   `Set.range f`, and `MonoidHom.mem_range` at line 78 states the
   characterization. The required equation `normUnits K K x = x` is the
   imported public theorem `normUnits_self_apply : NormUnitsSelfApplyStatement.{u}`
   from `NormQuotient.U025.Proofs`, applied to `K` and `x`.

No new norm construction, helper lemma, instance or simp registration is
needed. A development check in the approved environment compiled the module
with no errors or warnings. The theorem uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. That check does not replace
the validator's exact-target check or independent review.

## Pinned original and theorem map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:237–245`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L237-L245):
the docstring is at 237, the theorem and its complete telescope at 238, the
equation at 239 and the proof at 240–245. The original is

```lean
theorem localNormSubgroup_self (K : Type u) [Field K] :
    localNormSubgroup K K = ⊤ := by
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact ⟨x, normUnits_self_apply K x⟩
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The same file defines the norm subgroup at lines 26–28 and proves the
witness theorem `normUnits_self_apply` at lines 231–235. The support norm
comes from `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`; that
complete file was also read and has SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `localNormSubgroup_self` | `localNormSubgroup_self : LocalNormSubgroupSelfStatement.{u}`, proved here |
| Its theorem telescope and equation | Existing closed `LocalNormSubgroupSelfStatement.{u}` in U026.Statements, unchanged |
| `localNormSubgroup` | Existing public U001.Definitions construction, unchanged |
| `normUnits` | Existing public NormUnits.U002.Definitions construction, unchanged |
| `normUnits_self_apply` | Existing public U025.Proofs theorem, unchanged, used as the witness |

Worker 248 adapted the proof directly from the pinned original on
1 November 2026. The namespace gains the `Langlands.NYLL` prefix. The
theorem proves the already published proposition by introducing its two
original binders and keeps the original six-line proof verbatim. In the
adapted Library, `normUnits_self_apply K x` is applied through the closed
`NormUnitsSelfApplyStatement.{u}`, which unfolds to the original binders
`K`, `[Field K]` and `x`. The sole U026.Statements import preserves the
predecessor chain. The noncomputable section, unused universe `v` and all
unrelated declarations are omitted. There is no new statement, instance,
simp registration, M093.027 or later unit, or host adapter. M093 has no
patch10 change. No shared adaptation draft or another worker's unpublished
work was reused.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. Worker 248 adapted
this proof and wrote this companion. There are no other project coauthors
or reused-draft contributors; dependency authors and notices remain
unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This generic identity-extension image equality supplies no named Artin
map, exact norm-kernel theorem for that map, host reciprocity quotient
construction, host evaluation formula or continuity theorem. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains its named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, the actual unit-norm image, exact norm kernel, quotient topology,
finite discrete Galois topology, host quotient construction, evaluation,
bijectivity and both continuity directions. The initial Type 0 host stage
does not discharge arbitrary-universe transport. No normalization, inertia,
cohomological comparison or reciprocity theorem follows from this proof.
Existing cohomological definitions and frozen targets retain their meaning.
M093.027 and later units and host adapters require separate work.
Compilation does not establish independent semantic acceptance or
publication.
