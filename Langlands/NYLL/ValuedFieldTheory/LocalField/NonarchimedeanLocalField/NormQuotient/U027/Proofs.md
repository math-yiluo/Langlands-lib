# Norm classes for the identity extension

This module proves the exact published closed target
`Langlands.NYLL.LocalFieldTheory.NormQuotientSelfEqOneStatement.{u}` with the
single theorem
`Langlands.NYLL.LocalFieldTheory.normQuotient_self_eq_one`.
It is the proof phase of M093.027 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U027.Statements`.
That module's Lean/Markdown pair and all imported pairs are unchanged.

## Complete interface and mathematical meaning

The theorem has exactly this unapplied type:

```lean
normQuotient_self_eq_one : NormQuotientSelfEqOneStatement.{u}
```

It has no external term or instance parameters and retains the sole
arbitrary universe `u`. The published proposition unfolds to

```lean
∀ (K : Type u) [Field K] (x : NormQuotient K K), x = 1
```

The three binders are internal, in the order explicit `K`,
instance-implicit `Field K` and explicit `x`. The canonical self-algebra of
`K` is inferred from the field structure; there is no supplied arbitrary
`[Algebra K K]`. No finite-dimensionality, finite-module, valuation,
topology, local-field, separability or Galois hypothesis is added. The
module's local-field context does not restrict this generic result.

The reused public `Langlands.NYLL.LocalFieldTheory.NormQuotient`, in
`NormQuotient.U002.Definitions`, is exactly `Kˣ ⧸ localNormSubgroup K L`.
Its public commutative-group instance `normQuotientCommGroup`, in
U003.Definitions, supplies the identity `1` in the equation. The public
`localNormSubgroup`, in U001.Definitions, is `(normUnits K L).range`, and
the public `normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`. All four declarations are
unchanged. So `x` is a class in the actual quotient of `Kˣ` by the image
of the unit norm of `K` over itself. The equation `x = 1` is equality in
that quotient group. The theorem says that this quotient is trivial:
every norm class for the identity extension is the identity class.

## Implemented proof

The implementation introduces the three binders with `intro K _ x` and then
keeps the original proof unchanged:

1. `refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_` applies
   the imported public protected theorem
   `NormQuotient.inductionOn : NormQuotientInductionOnStatement.{u}` from
   `NormQuotient.U016.Proofs`. Its closed statement unfolds to the original
   binders: implicit `K`, `L`, three instance arguments, the implicit
   `motive`, the class `q` and the hypothesis `h`. Here `L` is `K`, the
   motive is `fun q => q = 1` and the class is `x`. The remaining goal is
   `∀ a : Kˣ, normClass K K a = 1`, where `normClass` is the public
   quotient map `Kˣ →* NormQuotient K K` from `NormQuotient.U005.Definitions`.
2. `intro a` fixes a representative unit `a : Kˣ`.
3. `(normClass_eq_one_iff_mem K K a).2` uses the reverse direction of the
   imported public theorem
   `normClass_eq_one_iff_mem : NormClassEqOneIffMemStatement.{u}` from
   `NormQuotient.U022.Proofs`. It reduces `normClass K K a = 1` to
   `a ∈ localNormSubgroup K K`.
4. `rw [localNormSubgroup_self K]` rewrites with the imported public
   theorem `localNormSubgroup_self : LocalNormSubgroupSelfStatement.{u}` from
   `NormQuotient.U026.Proofs`, applied to `K`. Its equation
   `localNormSubgroup K K = ⊤` turns the goal into `a ∈ ⊤`.
5. `exact Subgroup.mem_top a` closes it with Mathlib's `Subgroup.mem_top`, at
   the approved pin in `Mathlib/Algebra/Group/Subgroup/Lattice.lean:143`.

All three public theorems are closed statements; each application unfolds
the corresponding Prop-valued definition to its original binders. No new
norm construction, helper lemma, instance or simp registration is needed.
A development check in the approved environment compiled the module with
no errors or warnings. The theorem's type is exactly the constant
`NormQuotientSelfEqOneStatement.{u}`, and it uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. That check does not
replace the validator's exact-target check or independent review.

## Pinned original and theorem map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:247–254`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L247-L254):
the docstring is at 247, the theorem and its complete telescope at 248, the
equation at 249 and the proof at 250–254. The original is

```lean
theorem normQuotient_self_eq_one (K : Type u) [Field K] (x : NormQuotient K K) :
    x = 1 := by
  refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_
  intro a
  exact (normClass_eq_one_iff_mem K K a).2 (by
    rw [localNormSubgroup_self K]
    exact Subgroup.mem_top a)
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The same file defines the norm subgroup at lines 26–28, the quotient at
30–32, its commutative-group structure at 34–38 and `normClass` at 49–54.
It proves quotient induction at 160–169, the membership criterion at
206–211 and the self-norm subgroup equality at 237–245. The support norm
comes from `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`; that
complete file was also read and has SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normQuotient_self_eq_one` | `normQuotient_self_eq_one : NormQuotientSelfEqOneStatement.{u}`, proved here |
| Its theorem telescope and equation | Existing closed `NormQuotientSelfEqOneStatement.{u}` in U027.Statements, unchanged |
| `NormQuotient` | Existing public U002.Definitions construction, unchanged |
| `normQuotientCommGroup` | Existing public U003.Definitions instance, unchanged |
| `localNormSubgroup` | Existing public U001.Definitions construction, unchanged |
| `normClass` | Existing public U005.Definitions construction, unchanged |
| `normUnits` | Existing public NormUnits.U002.Definitions construction, unchanged |
| `NormQuotient.inductionOn` | Existing public protected U016.Proofs theorem, unchanged |
| `normClass_eq_one_iff_mem` | Existing public U022.Proofs theorem, unchanged |
| `localNormSubgroup_self` | Existing public U026.Proofs theorem, unchanged |

Worker 248 adapted the proof directly from the pinned original on
1 November 2026. The namespace gains the `Langlands.NYLL` prefix. The
theorem proves the already published proposition by introducing its three
original binders and keeps the original five-line proof verbatim. The sole
U027.Statements import preserves the predecessor chain. The noncomputable
section, unused universe `v` and all unrelated declarations are omitted,
including the subsingleton instance at lines 256–260. There is no new
statement, instance, simp registration, M093.028 or later unit, or host
adapter. M093 has no patch10 change. No shared adaptation draft or another
worker's unpublished work was reused.

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

This generic identity-extension quotient result supplies no named Artin
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
M093.028 and later units, including the subsingleton instance, and host
adapters require separate work. Compilation does not establish independent
semantic acceptance or publication.
